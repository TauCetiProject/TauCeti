/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Transfer
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.GroupTheory.Abelianization.Basic
import TauCeti.NumberTheory.ClassFieldTheory.Global.LocalArtin.Norm

/-!
# Compatibility of finite abelian global Artin maps in towers

Let `K ⊆ E ⊆ L` be a tower of number fields with `L/K` finite abelian Galois. Then `E/K` and `L/E`
are also finite abelian Galois (`IsAbelianGalois.tower_bot`, `IsAbelianGalois.tower_top`), and the
three finite global Artin maps

* `ideleClassArtinMap K L : C_K →* Gal(L/K)`,
* `ideleClassArtinMap K E : C_K →* Gal(E/K)`, and
* `ideleClassArtinMap E L : C_E →* Gal(L/E)`

fit into three commuting squares corresponding to restriction, norm, and transfer. Top-field
restriction (`restrictNormalHom_ideleClassArtinMap`, `algEquivRestrictNormalHom_ideleClassArtinMap`,
`restrictNormal_ideleClassArtinMap`) is established in
`TauCeti.NumberTheory.ClassFieldTheory.Global.Reciprocity`; this file completes the picture in the
ground field:

1. **Ground-field norm** (`ideleClassArtinMap_ideleClassNormMap`): the Artin symbol in `Gal(L/K)`
   of `N_{E/K}(c)` is `ideleClassArtinMap E L c`, viewed in `Gal(L/K)` via
   `AlgEquiv.restrictScalars K`.
2. **Ground-field extension / transfer** (`of_ideleClassArtinMap_ideleClassExtension`,
   `restrictScalars_ideleClassArtinMap_ideleClassExtension`): the Artin symbol in `Gal(L/E)` of
   `ideleClassExtension K E c` is the group-theoretic transfer of `ideleClassArtinMap K L c`; read
   inside the commutative group `Gal(L/K)` via `AlgEquiv.restrictScalars K`, it equals
   `ideleClassArtinMap K L c ^ [E : K]`.

Since `AlgEquiv.restrictScalars K : Gal(L/E) →* Gal(L/K)` is injective and `ker(Art_{L/E}) =
N_{L/E}(C_L)`, an idele class `c ∈ C_K` becomes a norm from `L` after extension to `E` if and only
if `ideleClassArtinMap K L c ^ [E : K] = 1` (`ideleClassExtension_mem_range_ideleClassNormMap_iff`).
In particular, whenever the exponent of `Gal(L/K)` divides `[E : K]`, the transfer Artin map
`C_K →* Gal(L/E)` is identically trivial and every idele class of `K` becomes a norm from `L` over
`E` (`ideleClassArtinMap_ideleClassExtension_eq_one_of_exponent_dvd`,
`ideleClassExtension_mem_range_ideleClassNormMap_of_exponent_dvd`).

## Main results

* `TauCeti.ClassFieldTheory.ideleClassArtinMap_comp_ideleClassNormMap`,
  `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassNormMap`,
  `TauCeti.ClassFieldTheory.range_ideleClassArtinMap_comp_ideleClassNormMap`,
  `TauCeti.ClassFieldTheory.range_ideleClassArtinMap_comp_ideleClassNormMap_intermediateField`:
  compatibility of `ideleClassArtinMap` with `ideleClassNormMap` and identification of the
  norm-Artin image with `E.fixingSubgroup`.
* `TauCeti.ClassFieldTheory.of_ideleClassArtinMap_ideleClassExtension`,
  `TauCeti.ClassFieldTheory.restrictScalars_ideleClassArtinMap_ideleClassExtension`: compatibility
  of `ideleClassArtinMap` with `ideleClassExtension` and the transfer / `[E : K]`-th power map.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_eq_one_iff`,
  `TauCeti.ClassFieldTheory.ideleClassExtension_mem_range_ideleClassNormMap_iff`: criteria for
  triviality of the transferred Artin symbol and for `i_{E/K}(c) ∈ N_{L/E}(C_L)`.
* `TauCeti.ClassFieldTheory.ideleClassArtinMap_ideleClassExtension_eq_one_of_exponent_dvd`,
  `TauCeti.ClassFieldTheory.ideleClassExtension_mem_range_ideleClassNormMap_of_exponent_dvd`:
  vanishing of the transfer map when `Monoid.exponent Gal(L/K) ∣ [E : K]`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §5.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField GlobalNumberFields
open scoped IsMulCommutative

section GroundField

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [Algebra K E]
  {L : Type} [Field L] [NumberField L] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
  [IsAbelianGalois K L] [IsAbelianGalois E L]

/-- **Norm functoriality of `ideleClassArtinMap` in the ground field (homomorphism form).** Let
`K ⊆ E ⊆ L` be number fields with `L/K` finite abelian Galois. Composing `ideleClassArtinMap K L`
with `ideleClassNormMap K E` equals `ideleClassArtinMap E L` followed by the inclusion
`AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)`. The instance `IsAbelianGalois E L` follows
from `IsAbelianGalois K L` (`IsAbelianGalois.tower_top`). -/
theorem ideleClassArtinMap_comp_ideleClassNormMap :
    (ideleClassArtinMap K L).comp
        (ideleClassNormMap K E : IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K) =
      (AlgEquiv.restrictScalarsHom K).comp (ideleClassArtinMap E L) := by
  refine MonoidHom.ext fun c ↦ Group.Abelianization.of_injective ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← Group.Abelianization.map_of (AlgEquiv.restrictScalarsHom K),
    of_ideleClassArtinMap K L IsSepClosed.lift, of_ideleClassArtinMap E L IsSepClosed.lift]
  have h := globalArtinMap_ideleClassNormMap (K := K) (E := E) (L := L)
    IsSepClosed.lift IsSepClosed.lift c
  simpa only [MonoidHom.coe_toAdditive, MonoidHom.coe_ofClass, Function.comp_apply,
    toMul_ofMul] using congrArg Additive.toMul h

/-- **Norm functoriality of `ideleClassArtinMap` in the ground field.** The Artin symbol in
`Gal(L/K)` of `N_{E/K}(c)` is `ideleClassArtinMap E L c`, viewed as a `K`-automorphism of `L`. -/
@[simp]
theorem ideleClassArtinMap_ideleClassNormMap (c : IdeleClassGroup (𝓞 E) E) :
    ideleClassArtinMap K L (ideleClassNormMap K E c) =
      AlgEquiv.restrictScalars K (ideleClassArtinMap E L c) :=
  DFunLike.congr_fun ideleClassArtinMap_comp_ideleClassNormMap c

/-- **Transfer functoriality of `ideleClassArtinMap` on abelianizations.** In a tower `K ⊆ E ⊆ L`
with `L/K` finite abelian Galois, the class of `ideleClassArtinMap E L (ideleClassExtension K E c)`
in `Gal(L/E)^ab` is the group-theoretic transfer of the class of `ideleClassArtinMap K L c` along
`Gal(L/E) ↪ Gal(L/K)`. -/
theorem of_ideleClassArtinMap_ideleClassExtension (c : IdeleClassGroup (𝓞 K) K) :
    Group.Abelianization.of (ideleClassArtinMap E L (ideleClassExtension K E c)) =
      Group.Abelianization.transferOfInjective
        (f := (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)))
        (AlgEquiv.restrictScalarsHom_injective K)
        (Group.Abelianization.of (ideleClassArtinMap K L c)) := by
  rw [of_ideleClassArtinMap E L IsSepClosed.lift, of_ideleClassArtinMap K L IsSepClosed.lift]
  have h := globalArtinMap_ideleClassExtension (K := K) (E := E) (L := L)
    IsSepClosed.lift IsSepClosed.lift c
  simpa only [MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul] using
    congrArg Additive.toMul h

/-- **Transfer functoriality of `ideleClassArtinMap` read in `Gal(L/K)`.** In an abelian tower
`K ⊆ E ⊆ L`, the global Artin symbol over `E` of `ideleClassExtension K E c`, viewed inside
`Gal(L/K)` via the injective map `AlgEquiv.restrictScalars K`, equals the `[E : K]`-th power of
`ideleClassArtinMap K L c`:

```text
restrictScalars K (Art_{L/E} (i_{E/K} c)) = (Art_{L/K} c) ^ [E : K].
```
-/
@[simp]
theorem restrictScalars_ideleClassArtinMap_ideleClassExtension (c : IdeleClassGroup (𝓞 K) K) :
    AlgEquiv.restrictScalars K (ideleClassArtinMap E L (ideleClassExtension K E c)) =
      ideleClassArtinMap K L c ^ Module.finrank K E := by
  refine Group.Abelianization.of_injective ?_
  rw [← AlgEquiv.restrictScalarsHom_apply, ← Group.Abelianization.map_of,
    of_ideleClassArtinMap_ideleClassExtension,
    Group.Abelianization.map_transferOfInjective,
    AlgEquiv.index_range_restrictScalarsHom K E L, map_pow]

/-- In an abelian tower `K ⊆ E ⊆ L`, the transferred Artin symbol
`ideleClassArtinMap E L (ideleClassExtension K E c)` is trivial if and only if
`ideleClassArtinMap K L c ^ [E : K] = 1`. -/
theorem ideleClassArtinMap_ideleClassExtension_eq_one_iff (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassArtinMap E L (ideleClassExtension K E c) = 1 ↔
      ideleClassArtinMap K L c ^ Module.finrank K E = 1 := by
  rw [← (AlgEquiv.restrictScalars_injective (R := K) (S := E) (A := L)).eq_iff,
    restrictScalars_ideleClassArtinMap_ideleClassExtension,
    ← AlgEquiv.restrictScalarsHom_apply, map_one]

omit [IsAbelianGalois E L] in
/-- **Norm criterion for extended idele classes in an abelian tower.** Let `K ⊆ E ⊆ L` be number
fields with `L/K` finite abelian Galois. An idele class `c ∈ C_K`, extended to `E`, is a norm from
`L` if and only if `ideleClassArtinMap K L c ^ [E : K] = 1`. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_iff (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K E c ∈ (ideleClassNormMap E L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range ↔
      ideleClassArtinMap K L c ^ Module.finrank K E = 1 := by
  have := IsAbelianGalois.tower_top K E L
  rw [← ker_ideleClassArtinMap E L, MonoidHom.mem_ker,
    ideleClassArtinMap_ideleClassExtension_eq_one_iff]

/-- **Vanishing of the transfer Artin map under an exponent bound.** If the exponent of `Gal(L/K)`
divides `[E : K]`, then `ideleClassArtinMap E L (ideleClassExtension K E c) = 1` for every
`c ∈ C_K`. -/
theorem ideleClassArtinMap_ideleClassExtension_eq_one_of_exponent_dvd
    (hexp : Monoid.exponent Gal(L/K) ∣ Module.finrank K E) (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassArtinMap E L (ideleClassExtension K E c) = 1 :=
  (ideleClassArtinMap_ideleClassExtension_eq_one_iff c).mpr
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp _)

omit [IsAbelianGalois E L] in
/-- **Norm principalization of extended idele classes under an exponent bound.** If the exponent of
`Gal(L/K)` divides `[E : K]`, then every idele class of `K` becomes a norm from `L` upon extension
to `E`. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_of_exponent_dvd
    (hexp : Monoid.exponent Gal(L/K) ∣ Module.finrank K E) (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K E c ∈ (ideleClassNormMap E L :
      IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 E) E).range :=
  (ideleClassExtension_mem_range_ideleClassNormMap_iff c).mpr
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp _)

omit [IsAbelianGalois E L] in
/-- **Image of the norm group under `ideleClassArtinMap`.** In an abelian tower `K ⊆ E ⊆ L`, the
image of `N_{E/K}(C_E)` under `ideleClassArtinMap K L` is the image of `Gal(L/E)` in `Gal(L/K)`
under `AlgEquiv.restrictScalarsHom K`. -/
theorem range_ideleClassArtinMap_comp_ideleClassNormMap :
    ((ideleClassArtinMap K L).comp
        (ideleClassNormMap K E : IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K)).range =
      (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)).range := by
  have := IsAbelianGalois.tower_top K E L
  rw [ideleClassArtinMap_comp_ideleClassNormMap, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (ideleClassArtinMap_surjective E L), Subgroup.map_top]

end GroundField

/-- For an intermediate field `E` of a finite abelian extension `L/K`, the image of `N_{E/K}(C_E)`
under `ideleClassArtinMap K L` is `E.fixingSubgroup`. -/
theorem range_ideleClassArtinMap_comp_ideleClassNormMap_intermediateField
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (E : IntermediateField K L) :
    ((ideleClassArtinMap K L).comp
        (ideleClassNormMap K E : IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K)).range =
      E.fixingSubgroup := by
  rw [range_ideleClassArtinMap_comp_ideleClassNormMap,
    AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K E L,
    IntermediateField.restrictNormalHom_ker]

end TauCeti.ClassFieldTheory
