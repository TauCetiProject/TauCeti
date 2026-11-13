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
`ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois`).

To instantiate this at the second step of the Hilbert class field tower, we also realize the ray
class fields — and hence the ordinary and narrow Hilbert class fields — of any number field `L`
in a tower `K → L → Kˢ` inside `Kˢ` itself (`rayClassFieldOver`, `hilbertClassFieldOver`,
`narrowHilbertClassFieldOver`):

* `rayClassFieldOver K 𝔪` is `L`-isomorphic to `rayClassField 𝔪`
  (`rayClassFieldOverEquivOfAlgHom`), so its idele-class norm group over `L` is `raySubgroup 𝔪`
  (`range_ideleClassNormMap_rayClassFieldOver`).
* `hilbertClassFieldOver K L` and `narrowHilbertClassFieldOver K L` remain unramified at finite
  primes over `K` whenever `L/K` is (`isUnramifiedAt_hilbertClassFieldOver`,
  `isUnramifiedAt_narrowHilbertClassFieldOver`), and `hilbertClassFieldOver K L` remains
  unramified at infinite places over `K` whenever `L/K` is
  (`isUnramifiedAtInfinitePlaces_hilbertClassFieldOver`).
* When `L/K` is Galois, both `hilbertClassFieldOver K L` and `narrowHilbertClassFieldOver K L` are
  Galois over `K` (`isGalois_hilbertClassFieldOver`, `isGalois_narrowHilbertClassFieldOver`), by
  transporting their universal unramified-abelian characterizations along automorphisms of `Kˢ/K`.

## Main definitions

* `TauCeti.ClassFieldTheory.rayClassFieldOver`: the ray class field of a modulus `𝔪` of `L`
  realized inside `SeparableClosure K`.
* `TauCeti.ClassFieldTheory.hilbertClassFieldOver`,
  `TauCeti.ClassFieldTheory.narrowHilbertClassFieldOver`: the ordinary and narrow Hilbert class
  fields of `L` inside `SeparableClosure K`.
* `TauCeti.ClassFieldTheory.rayClassFieldOverEquivOfAlgHom`: the `L`-algebra isomorphism
  `rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪` induced by any `L`-embedding into `Kˢ`.

## Main results

* `TauCeti.ClassFieldTheory.ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois`: extended
  idele classes in `hilbertClassField K` are norms from any everywhere-unramified finite Galois
  intermediate field containing `hilbertClassField K`.
* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_rayClassFieldOver`: the idele-class norm group
  of `rayClassFieldOver K 𝔪` over `L` is `raySubgroup 𝔪`.
* `TauCeti.ClassFieldTheory.isUnramifiedAt_hilbertClassFieldOver`,
  `TauCeti.ClassFieldTheory.isUnramifiedAtInfinitePlaces_hilbertClassFieldOver`: preservation of
  unramifiedness in the Hilbert tower.
* `TauCeti.ClassFieldTheory.isGalois_hilbertClassFieldOver`,
  `TauCeti.ClassFieldTheory.isGalois_narrowHilbertClassFieldOver`: Galoisness over `K` when `L/K`
  is Galois.

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
theorem ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [NumberField E]
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
def toRayClassFieldOver : L →ₐ[K] rayClassFieldOver K 𝔪 where
  toFun a := ⟨algebraMap L (SeparableClosure K) a, algebraMap_mem_rayClassFieldOver K 𝔪 a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' k := Subtype.ext <|
    (IsScalarTower.algebraMap_apply K L (SeparableClosure K) k).symm.trans
      (IntermediateField.coe_algebraMap_apply _ k).symm

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
  let f : rayClassField 𝔪 →ₐ[L] rayClassFieldOver K 𝔪 :=
    { toFun x := ⟨ι x, by
        rw [rayClassFieldOver_eq_fieldRange K 𝔪 ι, IntermediateField.mem_restrictScalars]
        exact ⟨x, rfl⟩⟩
      map_one' := Subtype.ext ι.map_one
      map_mul' x y := Subtype.ext (ι.map_mul x y)
      map_zero' := Subtype.ext ι.map_zero
      map_add' x y := Subtype.ext (ι.map_add x y)
      commutes' a := Subtype.ext <|
        (ι.commutes a).trans <|
          (IsScalarTower.algebraMap_apply L (rayClassFieldOver K 𝔪) (SeparableClosure K) a).trans
            (IntermediateField.algebraMap_apply _ _) }
  AlgEquiv.ofBijective f ⟨f.injective, fun ⟨z, hz⟩ ↦ by
    rw [rayClassFieldOver_eq_fieldRange K 𝔪 ι, IntermediateField.mem_restrictScalars] at hz
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩⟩

/-- In `SeparableClosure K`, `rayClassFieldOverEquivOfAlgHom K 𝔪 ι` acts as `ι`. -/
@[simp]
theorem coe_rayClassFieldOverEquivOfAlgHom_apply (ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K)
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] (x : rayClassField 𝔪) :
    (rayClassFieldOverEquivOfAlgHom K 𝔪 ι x : SeparableClosure K) = ι x :=
  (rfl)

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
instance numberField_rayClassFieldOver : NumberField (rayClassFieldOver K 𝔪) := by
  let _ : Algebra L (rayClassFieldOver K 𝔪) := (toRayClassFieldOver K 𝔪).toRingHom.toAlgebra
  have : IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IntermediateField.algebraMap_apply _ (toRayClassFieldOver K 𝔪 x)).symm
  have : FiniteDimensional L (rayClassFieldOver K 𝔪) :=
    Module.Finite.equiv (rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift).toLinearEquiv
  exact .of_module_finite L _

/-- `rayClassFieldOver K 𝔪` is finite-dimensional over `K`. -/
instance finiteDimensional_rayClassFieldOver :
    FiniteDimensional K (rayClassFieldOver K 𝔪) := by
  have : CharZero K := charZero_of_inj_zero fun n hn ↦ by
    simpa using congrArg (algebraMap K L) hn
  have : IsScalarTower ℚ K (rayClassFieldOver K 𝔪) :=
    IsScalarTower.of_algebraMap_eq fun q ↦
      (map_ratCast (algebraMap K (rayClassFieldOver K 𝔪)) q).symm
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

variable (L) in
/-- **The Hilbert class field of `L`, realized inside `SeparableClosure K`.** -/
abbrev hilbertClassFieldOver : IntermediateField K (SeparableClosure K) :=
  rayClassFieldOver K (Modulus.one L)

variable (L) in
/-- **The narrow Hilbert class field of `L`, realized inside `SeparableClosure K`.** -/
abbrev narrowHilbertClassFieldOver : IntermediateField K (SeparableClosure K) :=
  rayClassFieldOver K (narrowModulus L)

variable (L) in
/-- Every prime of `hilbertClassFieldOver K L` is unramified over `𝓞 L`. -/
theorem isUnramifiedAt_hilbertClassFieldOver_base
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)]
    (w : HeightOneSpectrum (𝓞 (hilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal := by
  let e := rayClassFieldOverEquivOfAlgHom K (Modulus.one L) IsSepClosed.lift
  exact (RingEquiv.forall_heightOneSpectrum_isUnramifiedAt_iff
    (RingEquiv.refl L) e.toRingEquiv (RingHom.ext fun x ↦ (e.commutes x).symm)).mp
    (isUnramifiedAt_hilbertClassField L) w

variable (L) in
/-- Every prime of `narrowHilbertClassFieldOver K L` is unramified over `𝓞 L`. -/
theorem isUnramifiedAt_narrowHilbertClassFieldOver_base
    [Algebra L (narrowHilbertClassFieldOver K L)]
    [IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K)]
    (w : HeightOneSpectrum (𝓞 (narrowHilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal := by
  let e := rayClassFieldOverEquivOfAlgHom K (narrowModulus L) IsSepClosed.lift
  exact (RingEquiv.forall_heightOneSpectrum_isUnramifiedAt_iff
    (RingEquiv.refl L) e.toRingEquiv (RingHom.ext fun x ↦ (e.commutes x).symm)).mp
    (isUnramifiedAt_narrowHilbertClassField L) w

variable (L) in
/-- `hilbertClassFieldOver K L` is unramified over `L` at all infinite places. -/
instance isUnramifiedAtInfinitePlaces_hilbertClassFieldOver_base
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)] :
    IsUnramifiedAtInfinitePlaces L (hilbertClassFieldOver K L) := by
  let e := rayClassFieldOverEquivOfAlgHom K (Modulus.one L) IsSepClosed.lift
  exact IsUnramifiedAtInfinitePlaces.of_equiv_equiv
    (RingEquiv.refl L) e.toRingEquiv (RingHom.ext fun x ↦ (e.commutes x).symm)

variable (L) in
/-- If `L/K` is unramified at every height-one prime, then so is
`hilbertClassFieldOver K L / K`. -/
theorem isUnramifiedAt_hilbertClassFieldOver
    (hL : ∀ v : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) v.asIdeal)
    (w : HeightOneSpectrum (𝓞 (hilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  let _ : Algebra L (hilbertClassFieldOver K L) :=
    (toRayClassFieldOver K (Modulus.one L)).toRingHom.toAlgebra
  have : IsScalarTower K L (hilbertClassFieldOver K L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <|
      (IntermediateField.coe_algebraMap_apply _ x).trans
        (IsScalarTower.algebraMap_apply K L (SeparableClosure K) x)
  have : IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IntermediateField.algebraMap_apply _ (toRayClassFieldOver K (Modulus.one L) x)).symm
  have : Algebra.IsIntegral (𝓞 L) (𝓞 (hilbertClassFieldOver K L)) :=
    Algebra.IsIntegral.tower_top (R := ℤ)
  have : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal := hL (w.under (𝓞 L))
  have : Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
    isUnramifiedAt_hilbertClassFieldOver_base K L w
  exact Algebra.IsUnramifiedAt.comp (w.under (𝓞 L)).asIdeal w.asIdeal

variable (L) in
/-- If `L/K` is unramified at every height-one prime, then so is
`narrowHilbertClassFieldOver K L / K`. -/
theorem isUnramifiedAt_narrowHilbertClassFieldOver
    (hL : ∀ v : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) v.asIdeal)
    (w : HeightOneSpectrum (𝓞 (narrowHilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  let _ : Algebra L (narrowHilbertClassFieldOver K L) :=
    (toRayClassFieldOver K (narrowModulus L)).toRingHom.toAlgebra
  have : IsScalarTower K L (narrowHilbertClassFieldOver K L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <|
      (IntermediateField.coe_algebraMap_apply _ x).trans
        (IsScalarTower.algebraMap_apply K L (SeparableClosure K) x)
  have : IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IntermediateField.algebraMap_apply _ (toRayClassFieldOver K (narrowModulus L) x)).symm
  have : Algebra.IsIntegral (𝓞 L) (𝓞 (narrowHilbertClassFieldOver K L)) :=
    Algebra.IsIntegral.tower_top (R := ℤ)
  have : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal := hL (w.under (𝓞 L))
  have : Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
    isUnramifiedAt_narrowHilbertClassFieldOver_base K L w
  exact Algebra.IsUnramifiedAt.comp (w.under (𝓞 L)).asIdeal w.asIdeal

variable (L) in
/-- If `L/K` is unramified at all infinite places, then so is `hilbertClassFieldOver K L / K`. -/
instance isUnramifiedAtInfinitePlaces_hilbertClassFieldOver [IsUnramifiedAtInfinitePlaces K L] :
    IsUnramifiedAtInfinitePlaces K (hilbertClassFieldOver K L) := by
  let _ : Algebra L (hilbertClassFieldOver K L) :=
    (toRayClassFieldOver K (Modulus.one L)).toRingHom.toAlgebra
  have : IsScalarTower K L (hilbertClassFieldOver K L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <|
      (IntermediateField.coe_algebraMap_apply _ x).trans
        (IsScalarTower.algebraMap_apply K L (SeparableClosure K) x)
  have : IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IntermediateField.algebraMap_apply _ (toRayClassFieldOver K (Modulus.one L) x)).symm
  exact IsUnramifiedAtInfinitePlaces.trans K L (hilbertClassFieldOver K L)

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
  let φL : L →+* Hσ :=
    { toFun a := ⟨algebraMap L (SeparableClosure K) a, hmem a⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' _ _ := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' _ _ := Subtype.ext (map_add _ _ _) }
  let instAlg : Algebra L Hσ := φL.toAlgebra
  have instTower : IsScalarTower L Hσ (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (IntermediateField.algebraMap_apply Hσ (φL x)).symm
  let _ : Algebra L H := (toRayClassFieldOver K 𝔪).toRingHom.toAlgebra
  have : IsScalarTower L H (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (IntermediateField.algebraMap_apply H (toRayClassFieldOver K 𝔪 x)).symm
  let ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K := IsSepClosed.lift
  let g : rayClassField 𝔪 ≃+* Hσ :=
    (rayClassFieldOverEquivOfAlgHom K 𝔪 ι).toRingEquiv.trans
      (H.equivMap (σ : SeparableClosure K →ₐ[K] SeparableClosure K)).toRingEquiv
  refine ⟨instAlg, instTower, g, RingHom.ext fun a ↦ Subtype.ext ?_⟩
  have hLHS : ((algebraMap L Hσ (σ.restrictNormal L a) : Hσ) : SeparableClosure K) =
      algebraMap L (SeparableClosure K) (σ.restrictNormal L a) := rfl
  rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv, hLHS,
    RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    IntermediateField.coe_equivMap_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toRingEquiv,
    coe_rayClassFieldOverEquivOfAlgHom_apply, ι.commutes, AlgEquiv.restrictNormal_commutes]

variable (L) in
/-- **The Hilbert class field of a Galois subextension `L/K` is Galois over `K`.** Every conjugate
of `hilbertClassFieldOver K L` over `K` is an everywhere-unramified abelian extension of `L`, hence
lies in `hilbertClassFieldOver K L` by maximality of the Hilbert class field. -/
instance isGalois_hilbertClassFieldOver [IsGalois K L] :
    IsGalois K (hilbertClassFieldOver K L) := by
  have : Normal K (hilbertClassFieldOver K L) := by
    refine IntermediateField.normal_iff_forall_map_le'.mpr fun σ ↦ ?_
    obtain ⟨instAlg, instTower, g, hcomp⟩ :=
      exists_ringEquiv_map_rayClassFieldOver K (Modulus.one L) σ
    let Hσ := (hilbertClassFieldOver K L).map
      (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
    have : NumberField Hσ := .of_ringEquiv _ _ g
    let f : L ≃+* L := (σ.restrictNormal L).toRingEquiv
    have : IsAbelianGalois L Hσ := IsAbelianGalois.of_equiv_equiv f g hcomp
    have hfin : ∀ w : HeightOneSpectrum (𝓞 Hσ), Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
      (RingEquiv.forall_heightOneSpectrum_isUnramifiedAt_iff f g hcomp).mp
        (isUnramifiedAt_hilbertClassField L)
    have hinf : IsUnramifiedAtInfinitePlaces L Hσ :=
      IsUnramifiedAtInfinitePlaces.of_equiv_equiv f g hcomp
    have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
    let eSep : SeparableClosure K ≃ₐ[L] SeparableClosure L :=
      IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
    let j : Hσ →ₐ[L] SeparableClosure L :=
      eSep.toAlgHom.comp (IsScalarTower.toAlgHom L Hσ (SeparableClosure K))
    have hle := (fieldRange_le_hilbertClassField_iff j).mpr ⟨hfin, hinf⟩
    intro x hx
    have hx' : eSep x ∈ hilbertClassField L := hle ⟨⟨x, hx⟩, rfl⟩
    exact (eSep.symm.toAlgHom.comp (hilbertClassField L).val).fieldRange_le_normalClosure
      ⟨⟨eSep x, hx'⟩, eSep.symm_apply_apply x⟩
  exact {}

variable (L) in
/-- **The narrow Hilbert class field of a Galois subextension `L/K` is Galois over `K`.** Every
conjugate of `narrowHilbertClassFieldOver K L` over `K` is an abelian extension of `L` unramified
at all finite primes, hence lies in `narrowHilbertClassFieldOver K L` by maximality of the narrow
Hilbert class field. -/
instance isGalois_narrowHilbertClassFieldOver [IsGalois K L] :
    IsGalois K (narrowHilbertClassFieldOver K L) := by
  have : Normal K (narrowHilbertClassFieldOver K L) := by
    refine IntermediateField.normal_iff_forall_map_le'.mpr fun σ ↦ ?_
    obtain ⟨instAlg, instTower, g, hcomp⟩ :=
      exists_ringEquiv_map_rayClassFieldOver K (narrowModulus L) σ
    let Hσ := (narrowHilbertClassFieldOver K L).map
      (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
    have : NumberField Hσ := .of_ringEquiv _ _ g
    let f : L ≃+* L := (σ.restrictNormal L).toRingEquiv
    have : IsAbelianGalois L Hσ := IsAbelianGalois.of_equiv_equiv f g hcomp
    have hfin : ∀ w : HeightOneSpectrum (𝓞 Hσ), Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
      (RingEquiv.forall_heightOneSpectrum_isUnramifiedAt_iff f g hcomp).mp
        (isUnramifiedAt_narrowHilbertClassField L)
    have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
    let eSep : SeparableClosure K ≃ₐ[L] SeparableClosure L :=
      IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
    let j : Hσ →ₐ[L] SeparableClosure L :=
      eSep.toAlgHom.comp (IsScalarTower.toAlgHom L Hσ (SeparableClosure K))
    have hle := (fieldRange_le_narrowHilbertClassField_iff j).mpr hfin
    intro x hx
    have hx' : eSep x ∈ narrowHilbertClassField L := hle ⟨⟨x, hx⟩, rfl⟩
    exact (eSep.symm.toAlgHom.comp (narrowHilbertClassField L).val).fieldRange_le_normalClosure
      ⟨⟨eSep x, hx'⟩, eSep.symm_apply_apply x⟩
  exact {}

end RelativeClassFields

end TauCeti.ClassFieldTheory
