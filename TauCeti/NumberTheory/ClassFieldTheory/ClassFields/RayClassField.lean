/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.AdmissibleModulus.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.Correspondence

import TauCeti.NumberTheory.ClassFieldTheory.GlobalExistence.NormLimitation

/-!
# Ray class fields and the Hilbert class field

Let `K` be a number field and `𝔪` a modulus of `K`. The ray subgroup `U_𝔪` of the idele class
group `C_K` is open and of finite index, so the global class-field correspondence attaches to it a
unique finite abelian extension of `K` inside `Kˢ` with idele-class norm group `U_𝔪`: the
**ray class field** `rayClassField 𝔪`. It is the class field of the value of `globalClassField`
at `U_𝔪`, not an independent construction, and everything below is read off from the
correspondence.

* Its norm group is the ray subgroup (`range_ideleClassNormMap_rayClassField`), so `𝔪` is
  admissible for it (`isAdmissibleModulus_rayClassField`), and it is the only finite abelian
  extension of `K` with this norm group (`fieldRange_eq_rayClassField_iff`).
* It is the **largest abelian extension in which `𝔪` is admissible**: a finite abelian extension
  `L/K` embeds in `rayClassField 𝔪` exactly when `𝔪` is admissible for `L/K`
  (`isAdmissibleModulus_iff_le_rayClassField`), that is, by
  `isAdmissibleModulus_iff_abelianConductor_dvd`, exactly when the conductor of `L/K` divides `𝔪`.
* Ray class fields grow with the modulus (`rayClassField_mono`); more precisely
  `rayClassField 𝔪 ≤ rayClassField 𝔫` exactly when `U_𝔫 ≤ U_𝔪`
  (`rayClassField_le_rayClassField_iff`).
* The ray-class Artin map of `rayClassField 𝔪` at `𝔪` is an isomorphism
  `Cl_𝔪 ≃* Gal(rayClassField 𝔪 / K)` (`rayClassArtinEquiv`): its kernel is the image of the norm
  group, which is the ray subgroup, the kernel of the ray class map. Hence
  `[rayClassField 𝔪 : K] = #Cl_𝔪` (`finrank_rayClassField`).

The **Hilbert class field** `hilbertClassField K` is the ray class field of the trivial modulus,
and the **narrow Hilbert class field** `narrowHilbertClassField K` that of the modulus carrying
every real place and no finite place. The Artin map identifies the class group of `K` with the
Galois group of the Hilbert class field (`hilbertClassArtinEquiv`), whose degree is therefore the
class number (`finrank_hilbertClassField`).

## Main definitions

* `TauCeti.ClassFieldTheory.rayNormSubgroup`: the ray subgroup as an open finite-index subgroup.
* `TauCeti.ClassFieldTheory.rayClassField`: the ray class field of a modulus.
* `TauCeti.ClassFieldTheory.rayClassArtinEquiv`: `Cl_𝔪 ≃* Gal(rayClassField 𝔪 / K)`.
* `TauCeti.ClassFieldTheory.hilbertClassField`, `TauCeti.ClassFieldTheory.narrowHilbertClassField`:
  the (narrow) Hilbert class field.
* `TauCeti.ClassFieldTheory.hilbertClassArtinEquiv`: `Cl_K ≃* Gal(hilbertClassField K / K)`.

## Main results

* `TauCeti.ClassFieldTheory.range_ideleClassNormMap_rayClassField`: the norm group of the ray
  class field of `𝔪` is the ray subgroup of `𝔪`.
* `TauCeti.ClassFieldTheory.fieldRange_eq_rayClassField_iff`: the ray class field is the unique
  finite abelian extension with norm group the ray subgroup.
* `TauCeti.ClassFieldTheory.isAdmissibleModulus_iff_le_rayClassField`: `𝔪` is admissible for a
  finite abelian `L/K` exactly when `L` embeds in the ray class field of `𝔪`.
* `TauCeti.ClassFieldTheory.finrank_rayClassField` and
  `TauCeti.ClassFieldTheory.finrank_hilbertClassField`: the degrees are the order of the ray class
  group and the class number.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §6 (the ray class field).
* J. S. Milne, *Class Field Theory*, v4.03, Chapter V, §3.
-/

public noncomputable section

open NumberField TauCeti.GlobalNumberFields

namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]

/-! ### The ray class field -/

/-- The ray subgroup of a modulus, as an open subgroup of finite index of the idele class group:
the source carrier of the global class-field correspondence. -/
def rayNormSubgroup (𝔪 : Modulus K) : GlobalNormSubgroups K :=
  ⟨⟨raySubgroup 𝔪, isOpen_raySubgroup 𝔪⟩, inferInstance⟩

/-- The subgroup underlying `rayNormSubgroup 𝔪` is the ray subgroup of `𝔪`. -/
@[simp]
theorem rayNormSubgroup_toSubgroup (𝔪 : Modulus K) :
    (rayNormSubgroup 𝔪).1.toSubgroup = raySubgroup 𝔪 :=
  (rfl)

/-- **The ray class field of a modulus** `𝔪` of a number field `K`: the class field in `Kˢ` of
the ray subgroup of `𝔪` under the global class-field correspondence, that is, the unique finite
abelian extension of `K` in `Kˢ` whose idele-class norm group is the ray subgroup of `𝔪`
(`range_ideleClassNormMap_rayClassField`). -/
def rayClassField (𝔪 : Modulus K) : IntermediateField K (SeparableClosure K) :=
  classField K (globalClassField (rayNormSubgroup 𝔪)).1

/-- The ray class field of `𝔪` is the class field of the value of the global correspondence at the
ray subgroup of `𝔪`. -/
theorem rayClassField_def (𝔪 : Modulus K) :
    rayClassField 𝔪 = classField K (globalClassField (rayNormSubgroup 𝔪)).1 :=
  (rfl)

variable (𝔪 : Modulus K)

/-- The ray class field of `𝔪` is a finite extension of `K`. -/
instance finiteDimensional_rayClassField : FiniteDimensional K (rayClassField 𝔪) :=
  finiteDimensional_classField _

/-- The ray class field of `𝔪` is a number field. -/
instance numberField_rayClassField : NumberField (rayClassField 𝔪) :=
  numberField_classField _

/-- The ray class field of `𝔪` is an abelian extension of `K`. -/
instance isAbelianGalois_rayClassField : IsAbelianGalois K (rayClassField 𝔪) :=
  isAbelianGalois_classField_iff.2 (globalClassField (rayNormSubgroup 𝔪)).2

/-- **The norm group of the ray class field is the ray subgroup**: `N(C_{K_𝔪}) = U_𝔪`. -/
theorem range_ideleClassNormMap_rayClassField :
    (ideleClassNormMap K (rayClassField 𝔪) :
        IdeleClassGroup (𝓞 (rayClassField 𝔪)) (rayClassField 𝔪) →* IdeleClassGroup (𝓞 K) K).range =
      raySubgroup 𝔪 :=
  (globalNormSubgroup_eq_range_classField K _).symm.trans
    (globalClassField_normSubgroup (rayNormSubgroup 𝔪))

/-- A modulus is admissible for its own ray class field. -/
theorem isAdmissibleModulus_rayClassField : IsAdmissibleModulus K (rayClassField 𝔪) 𝔪 :=
  isAdmissibleModulus_iff.2 (range_ideleClassNormMap_rayClassField 𝔪).ge

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **The ray class field is the largest abelian extension in which `𝔪` is admissible**: for a
finite abelian extension `L/K` of number fields and any `K`-embedding `ι` of `L` into `Kˢ`, the
modulus `𝔪` is admissible for `L/K` exactly when `ι` maps `L` into the ray class field of `𝔪`. By
`isAdmissibleModulus_iff_abelianConductor_dvd`, this says that the abelian extensions of `K` with
conductor dividing `𝔪` are exactly the subextensions of the ray class field of `𝔪`. -/
theorem isAdmissibleModulus_iff_le_rayClassField (ι : L →ₐ[K] SeparableClosure K) :
    IsAdmissibleModulus K L 𝔪 ↔ ι.fieldRange ≤ rayClassField 𝔪 := by
  -- Read both norm groups as norm subgroups of layers, compare the abelian layers, and pass to
  -- their class fields, which reverses the inclusion.
  rw [isAdmissibleModulus_iff, ← globalNormSubgroup_fixingOpenNormalSubgroup,
    ← rayNormSubgroup_toSubgroup, ← globalClassField_normSubgroup,
    globalNormSubgroup_le_iff_of_isAbelian isAbelianClassFieldLayer_fixingOpenNormalSubgroup,
    ← classField_le_classField_iff, classField_fixingOpenNormalSubgroup ι, rayClassField_def]

/-- **The ray class field is characterized by its norm group**: a finite abelian extension `L/K`,
embedded in `Kˢ` by `ι`, is the ray class field of `𝔪` exactly when its idele-class norm group is
the ray subgroup of `𝔪`. -/
theorem fieldRange_eq_rayClassField_iff (ι : L →ₐ[K] SeparableClosure K) :
    ι.fieldRange = rayClassField 𝔪 ↔
      (ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range =
        raySubgroup 𝔪 := by
  -- Both sides say that the abelian layer of `L` is the value of the correspondence at `U_𝔪`.
  rw [← globalNormSubgroup_fixingOpenNormalSubgroup, ← rayNormSubgroup_toSubgroup,
    ← globalClassField_eq_iff (rayNormSubgroup 𝔪)
      ⟨_, isAbelianClassFieldLayer_fixingOpenNormalSubgroup⟩,
    ← classField_fixingOpenNormalSubgroup ι, rayClassField_def, eq_comm,
    (classField_injective K).eq_iff, Subtype.ext_iff]

variable {𝔪}

/-- **Inclusions of ray class fields are inclusions of ray subgroups**, reversed. -/
theorem rayClassField_le_rayClassField_iff {𝔫 : Modulus K} :
    rayClassField 𝔪 ≤ rayClassField 𝔫 ↔ raySubgroup 𝔫 ≤ raySubgroup 𝔪 :=
  (globalClassField_orderReversing (rayNormSubgroup 𝔫) (rayNormSubgroup 𝔪)).symm

/-- **Ray class fields grow with the modulus**: if `𝔪 ∣ 𝔫`, the ray class field of `𝔪` lies in
that of `𝔫`. -/
theorem rayClassField_mono {𝔫 : Modulus K} (h : 𝔪 ∣ 𝔫) : rayClassField 𝔪 ≤ rayClassField 𝔫 :=
  rayClassField_le_rayClassField_iff.2 (raySubgroup_antitone h)

/-! ### Ray-class reciprocity for the ray class field -/

variable (𝔪)

/-- **Ray-class reciprocity for the ray class field**: the ray-class Artin map
`Cl_𝔪 →* Gal(rayClassField 𝔪 / K)` is an isomorphism. It is surjective as every ray-class Artin
map is, and injective because its kernel is the image in `Cl_𝔪` of the norm group of the ray class
field, which is the ray subgroup, the kernel of the ray class map. -/
def rayClassArtinEquiv : RayClassGroup 𝔪 ≃* Gal(rayClassField 𝔪/K) :=
  MulEquiv.ofBijective (rayClassArtinMap 𝔪 (isAdmissibleModulus_rayClassField 𝔪))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 <| by
      rw [ker_rayClassArtinMap, range_ideleClassNormMap_rayClassField, Subgroup.map_eq_bot_iff,
        ker_rayClassQuotient],
      rayClassArtinMap_surjective _⟩

/-- `rayClassArtinEquiv 𝔪` is the ray-class Artin map of the ray class field of `𝔪`. -/
@[simp]
theorem rayClassArtinEquiv_apply (x : RayClassGroup 𝔪) :
    rayClassArtinEquiv 𝔪 x = rayClassArtinMap 𝔪 (isAdmissibleModulus_rayClassField 𝔪) x :=
  (rfl)

/-- **The degree of the ray class field of `𝔪` is the order of the ray class group of `𝔪`.** -/
theorem finrank_rayClassField :
    Module.finrank K (rayClassField 𝔪) = Nat.card (RayClassGroup 𝔪) := by
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr (rayClassArtinEquiv 𝔪).toEquiv]

/-! ### The Hilbert class field and the narrow Hilbert class field -/

variable (K)

/-- **The Hilbert class field** of a number field `K`: the ray class field of the trivial modulus,
the largest abelian extension of `K` in `Kˢ` in which the trivial modulus is admissible. It is
defined for every number field, in every degree. -/
abbrev hilbertClassField : IntermediateField K (SeparableClosure K) :=
  rayClassField (Modulus.one K)

/-- **The narrow Hilbert class field** of a number field `K`: the ray class field of the modulus
`narrowModulus K`, which is trivial at the finite places and carries every real place. -/
abbrev narrowHilbertClassField : IntermediateField K (SeparableClosure K) :=
  rayClassField (narrowModulus K)

variable {K} in
/-- The Hilbert class field lies in every ray class field. -/
theorem hilbertClassField_le_rayClassField : hilbertClassField K ≤ rayClassField 𝔪 :=
  rayClassField_mono (Modulus.one_dvd 𝔪)

/-- The Hilbert class field lies in the narrow Hilbert class field. -/
theorem hilbertClassField_le_narrowHilbertClassField :
    hilbertClassField K ≤ narrowHilbertClassField K :=
  hilbertClassField_le_rayClassField _

/-- **Reciprocity for the Hilbert class field**: the Artin map identifies the class group of `K`
with the Galois group of the Hilbert class field. It is `rayClassArtinEquiv` at the trivial
modulus, read on the class group through `oneEquivClassGroup`. -/
def hilbertClassArtinEquiv : ClassGroup (𝓞 K) ≃* Gal(hilbertClassField K/K) :=
  oneEquivClassGroup.symm.trans (rayClassArtinEquiv (Modulus.one K))

variable {K} in
/-- On the class group, `hilbertClassArtinEquiv` is the ray-class Artin map of the trivial
modulus. -/
@[simp]
theorem hilbertClassArtinEquiv_oneEquivClassGroup (x : RayClassGroup (Modulus.one K)) :
    hilbertClassArtinEquiv K (oneEquivClassGroup x) = rayClassArtinEquiv (Modulus.one K) x := by
  rw [hilbertClassArtinEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

/-- **The degree of the Hilbert class field is the class number.** -/
theorem finrank_hilbertClassField : Module.finrank K (hilbertClassField K) = classNumber K := by
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr (hilbertClassArtinEquiv K).toEquiv,
    classNumber, Nat.card_eq_fintype_card]

end TauCeti.ClassFieldTheory
