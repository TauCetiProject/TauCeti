/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.CoefficientMap
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Formation
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Periodic

/-!
# The obstruction to lifting idele-class cohomology to the ideles

Let `K` be a number field and `L/F` a finite Galois layer inside `Kˢ`, cut out by open subgroups
`V ◁ U` of `G_K`. The exact sequence `0 → (Kˢ)ˣ → I_{Kˢ} → C_{Kˢ} → 0` of discrete `G_K`-modules
stays exact on `V`-invariants, because Hilbert 90 kills `H¹(V, (Kˢ)ˣ)`: every idele class fixed by
`V` is the class of an idele fixed by `V` (`exists_ideleClassMk_eq_of_isClosed`). On the layer this
is the short exact sequence of `Gal(L/F)`-modules

```text
0 → Lˣ → I_L → C_L → 0
```

(`ideleShortComplex_shortExact`). Its long exact cohomology sequence contains

```text
H²(Gal(L/F), I_L) → H²(Gal(L/F), C_L) → H³(Gal(L/F), Lˣ),
```

whose first map is `ideleToClassH2` and whose second, the connecting homomorphism, is
`classToMultiplicativeH3`. The sum of local invariants is computed on `H²(Gal(L/F), I_L)` and
descends only to the image of `ideleToClassH2`; `range_ideleToClassH2` says that a class of
`H²(Gal(L/F), C_L)` lies in that image exactly when its obstruction in `H³(Gal(L/F), Lˣ)` vanishes.

The obstruction does not vanish in general: for the biquadratic field `ℚ(√13, √17)` every
decomposition group has order at most two, so the image of `H²(Gal, I_L)` is killed by `2`, while
`H²(Gal, C_L)` is cyclic of order `4`. For a cyclic layer it does vanish
(`surjective_ideleToClassH2_of_isCyclic`), since there `H³(Gal(L/F), Lˣ) ≅ H¹(Gal(L/F), Lˣ)` by
two-periodicity and the latter is zero by Hilbert 90.

## Main definitions

* `TauCeti.ClassFieldTheory.ideleShortExact K`: the sequence `0 → (Kˢ)ˣ → I_{Kˢ} → C_{Kˢ} → 0`
  of discrete `G_K`-modules.
* `TauCeti.ClassFieldTheory.principalIdeleHom K`, `TauCeti.ClassFieldTheory.ideleClassHom K`: its
  two maps, between the coefficient modules of `unitsFormation K`, `ideleFormation K` and
  `globalFormation K`.
* `TauCeti.ClassFieldTheory.ideleShortComplex K L`: the sequence `Lˣ → I_L → C_L` of a layer.
* `TauCeti.ClassFieldTheory.ideleToClassH2 K L`: the map `H²(Gal(L/F), I_L) → H²(Gal(L/F), C_L)`.
* `TauCeti.ClassFieldTheory.classToMultiplicativeH3 K L`: the connecting homomorphism
  `H²(Gal(L/F), C_L) → H³(Gal(L/F), Lˣ)`.

## Main statements

* `TauCeti.ClassFieldTheory.exists_ideleClassMk_eq_of_isClosed`: idele classes fixed by a closed
  subgroup of `G_K` are classes of ideles fixed by it.
* `TauCeti.ClassFieldTheory.ideleShortComplex_shortExact`: `0 → Lˣ → I_L → C_L → 0` is exact.
* `TauCeti.ClassFieldTheory.range_ideleToClassH2`: the image of `ideleToClassH2` is the kernel of
  `classToMultiplicativeH3`.
* `TauCeti.ClassFieldTheory.surjective_ideleToClassH2_of_isCyclic`: on a cyclic layer every class
  of `H²(Gal(L/F), C_L)` lifts to `H²(Gal(L/F), I_L)`.

## Implementation notes

The formation of the multiplicative groups is `unitsFormation K`; its coefficient module is
`(Kˢ)ˣ`, written additively as `UnitsCoeff K`, so `Lˣ` is its level at the top subgroup of the
layer.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public noncomputable section

open CategoryTheory TauCeti.ContCohomology

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]

/-! ### The exact sequence of ideles and idele classes -/

/-- **The sequence `0 → (Kˢ)ˣ → I_{Kˢ} → C_{Kˢ} → 0`** of discrete `G_K`-modules, given by the
principal ideles and the quotient map onto the idele classes. -/
def ideleShortExact :
    DiscreteShortExact (AbsoluteGaloisGroup K) (UnitsCoeff K) (IdeleCoeff K) (IdeleClassCoeff K)
    where
  incl := principalIdele K
  proj := ideleClassMk K
  incl_equivariant := map_smul (principalIdele K)
  proj_equivariant := map_smul (ideleClassMk K)
  incl_injective := principalIdele_injective
  proj_surjective := ideleClassMk_surjective
  exact _ := ideleClassMk_eq_zero_iff

/-- The inclusion of `ideleShortExact K` is the embedding of the principal ideles. -/
@[simp]
theorem ideleShortExact_incl : (ideleShortExact K).incl = principalIdele K :=
  (rfl)

/-- The projection of `ideleShortExact K` is the quotient map onto the idele classes. -/
@[simp]
theorem ideleShortExact_proj : (ideleShortExact K).proj = ideleClassMk K :=
  (rfl)

variable {K} in
/-- **Idele classes fixed by a closed subgroup lift to fixed ideles.** If a closed subgroup `V` of
`G_K` fixes an idele class `c`, then `c` is the class of an idele fixed by `V`. The obstruction is
the connecting map `H⁰(V, C_{Kˢ}) → H¹(V, (Kˢ)ˣ)`, whose target vanishes by Hilbert 90 for `V`.
In field notation: the idele classes of the fixed field `L` of `V` are `I_L / Lˣ`. -/
theorem exists_ideleClassMk_eq_of_isClosed (V : Subgroup (AbsoluteGaloisGroup K))
    (hV : IsClosed (V : Set (AbsoluteGaloisGroup K))) {c : IdeleClassCoeff K}
    (hc : ∀ v ∈ V, v • c = c) :
    ∃ x : IdeleCoeff K, (∀ v ∈ V, v • x = x) ∧ ideleClassMk K x = c := by
  have := subsingleton_H1_unitsCoeff_of_isClosed K V hV
  let S := (ideleShortExact K).restrict V
  obtain ⟨x, hx⟩ := S.explicitCoeff0_surjective_of_subsingleton
    ⟨c, (FixedPoints.mem_addSubgroup _ _ _).2 fun v ↦ hc v v.2⟩
  refine ⟨x, fun v hv ↦ (FixedPoints.mem_addSubgroup _ _ _).1 x.2 ⟨v, hv⟩, ?_⟩
  simpa [S] using congrArg Subtype.val hx

/-! ### The maps of formations -/

/-- **The principal ideles as a map of formations**: `(Kˢ)ˣ → I_{Kˢ}`, read on the coefficient
modules of `unitsFormation K` and `ideleFormation K`. -/
def principalIdeleHom : (unitsFormation K).toRep ⟶ (ideleFormation K).toRep :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((ideleCoeffEquivIdeleFormation K).toAddMonoidHom.comp <| (principalIdele K).toAddMonoidHom.comp
      (unitsCoeffEquivUnitsFormation K).symm.toAddMonoidHom).toIntLinearMap
    fun g x ↦ by
      obtain ⟨x, rfl⟩ := (unitsCoeffEquivUnitsFormation K).surjective x
      rw [← unitsCoeffEquivUnitsFormation_smul]
      simpa using ideleCoeffEquivIdeleFormation_smul K g (principalIdele K x)

/-- `principalIdeleHom K` sends a unit of `Kˢ` to its principal idele. -/
@[simp]
theorem principalIdeleHom_hom_apply (x : UnitsCoeff K) :
    (principalIdeleHom K).hom (unitsCoeffEquivUnitsFormation K x) =
      ideleCoeffEquivIdeleFormation K (principalIdele K x) := by
  simp [principalIdeleHom]

/-- **The quotient map onto the idele classes as a map of formations**: `I_{Kˢ} → C_{Kˢ}`, read
on the coefficient modules of `ideleFormation K` and `globalFormation K`. -/
def ideleClassHom : (ideleFormation K).toRep ⟶ (globalFormation K).toRep :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((ideleClassCoeffEquivGlobalFormation K).toAddMonoidHom.comp <|
      (ideleClassMk K).toAddMonoidHom.comp
        (ideleCoeffEquivIdeleFormation K).symm.toAddMonoidHom).toIntLinearMap
    fun g x ↦ by
      obtain ⟨x, rfl⟩ := (ideleCoeffEquivIdeleFormation K).surjective x
      rw [← ideleCoeffEquivIdeleFormation_smul]
      simpa using ideleClassCoeffEquivGlobalFormation_smul K g (ideleClassMk K x)

/-- `ideleClassHom K` sends an idele of `Kˢ` to its idele class. -/
@[simp]
theorem ideleClassHom_hom_apply (x : IdeleCoeff K) :
    (ideleClassHom K).hom (ideleCoeffEquivIdeleFormation K x) =
      ideleClassCoeffEquivGlobalFormation K (ideleClassMk K x) := by
  simp [ideleClassHom]

/-! ### The exact sequence `0 → Lˣ → I_L → C_L → 0` of a layer -/

variable (L : NormalLayer (AbsoluteGaloisGroup K))

/-- The exactness of `(Kˢ)ˣ → I_{Kˢ} → C_{Kˢ}`, read on the coefficient modules of the three
formations. -/
theorem exact_principalIdeleHom_ideleClassHom :
    Function.Exact (principalIdeleHom K).hom (ideleClassHom K).hom := by
  intro x
  obtain ⟨x, rfl⟩ := (ideleCoeffEquivIdeleFormation K).surjective x
  rw [ideleClassHom_hom_apply, AddEquiv.map_eq_zero_iff, ideleClassMk_eq_zero_iff]
  refine ⟨fun ⟨y, hy⟩ ↦ ⟨unitsCoeffEquivUnitsFormation K y, by rw [principalIdeleHom_hom_apply,
    hy]⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := (unitsCoeffEquivUnitsFormation K).surjective y
  rw [principalIdeleHom_hom_apply] at hy
  exact ⟨y, (ideleCoeffEquivIdeleFormation K).injective hy⟩

/-- **The sequence `Lˣ → I_L → C_L` of a layer**: the coefficient modules of the units, idele and
idele-class formations at the top of the layer, with the maps induced by the principal ideles and
the quotient map onto the idele classes. -/
-- The body is exposed so that the terms of the sequence unfold to the layer coefficient modules
-- `L.rep F`: the connecting map of the sequence is only typed as a map between the cohomology of
-- the layer in `globalFormation K` and in `unitsFormation K` through that unfolding.
@[expose]
def ideleShortComplex : ShortComplex (Rep ℤ L.Gal) :=
  ShortComplex.mk (L.repMap (principalIdeleHom K)) (L.repMap (ideleClassHom K))
    (L.repMap_comp_eq_zero (exact_principalIdeleHom_ideleClassHom K))

/-- **The sequence `0 → Lˣ → I_L → C_L → 0` of a layer is exact.** Exactness on the right is
Hilbert 90 for the top subgroup of the layer, through `exists_ideleClassMk_eq_of_isClosed`. -/
theorem ideleShortComplex_shortExact : (ideleShortComplex K L).ShortExact := by
  refine L.shortExact_repMap (fun x y h ↦ ?_) (exact_principalIdeleHom_ideleClassHom K)
    fun y hy ↦ ?_
  · obtain ⟨x, rfl⟩ := (unitsCoeffEquivUnitsFormation K).surjective x
    obtain ⟨y, rfl⟩ := (unitsCoeffEquivUnitsFormation K).surjective y
    rw [principalIdeleHom_hom_apply, principalIdeleHom_hom_apply] at h
    rw [principalIdele_injective ((ideleCoeffEquivIdeleFormation K).injective h)]
  · obtain ⟨c, rfl⟩ := (ideleClassCoeffEquivGlobalFormation K).surjective y
    obtain ⟨x, hx, rfl⟩ := exists_ideleClassMk_eq_of_isClosed L.top.toSubgroup L.top.isClosed
      (c := c) fun v hv ↦ (ideleClassCoeffEquivGlobalFormation K).injective <| by
        rw [ideleClassCoeffEquivGlobalFormation_smul]
        exact (globalFormation K).mem_level.1 hy v hv
    refine ⟨ideleCoeffEquivIdeleFormation K x, (ideleFormation K).mem_level.2 fun v hv ↦ ?_,
      ideleClassHom_hom_apply K x⟩
    rw [← ideleCoeffEquivIdeleFormation_smul, hx v hv]

/-! ### The lifting obstruction -/

/-- **The comparison `H²(Gal(L/F), I_L) → H²(Gal(L/F), C_L)`** induced by the quotient map
`I_L → C_L` onto the idele classes of the layer. -/
def ideleToClassH2 : L.H (ideleFormation K) 2 →+ L.H (globalFormation K) 2 :=
  ((groupCohomology.functor ℤ L.Gal 2).map (L.repMap (ideleClassHom K))).hom.toAddMonoidHom

/-- `ideleToClassH2 K L` is the map induced in degree two by the quotient map onto the idele
classes of the layer. -/
theorem ideleToClassH2_def :
    ideleToClassH2 K L =
      ((groupCohomology.functor ℤ L.Gal 2).map (L.repMap (ideleClassHom K))).hom.toAddMonoidHom :=
  (rfl)

/-- **The obstruction to lifting**: the connecting homomorphism
`H²(Gal(L/F), C_L) → H³(Gal(L/F), Lˣ)` of the exact sequence `0 → Lˣ → I_L → C_L → 0`. Its target
is the third cohomology of the layer in the multiplicative formation `unitsFormation K`. -/
def classToMultiplicativeH3 : L.H (globalFormation K) 2 →+ L.H (unitsFormation K) 3 :=
  (groupCohomology.δ (ideleShortComplex_shortExact K L) 2 3 rfl).hom.toAddMonoidHom

/-- `classToMultiplicativeH3 K L` is Mathlib's connecting homomorphism `groupCohomology.δ` of the
exact sequence `0 → Lˣ → I_L → C_L → 0`. -/
theorem classToMultiplicativeH3_def :
    classToMultiplicativeH3 K L =
      (groupCohomology.δ (ideleShortComplex_shortExact K L) 2 3 rfl).hom.toAddMonoidHom :=
  (rfl)

/-- **Exactness at the idele-class layer**: a class of `H²(Gal(L/F), C_L)` lifts to
`H²(Gal(L/F), I_L)` exactly when its obstruction in `H³(Gal(L/F), Lˣ)` vanishes. -/
theorem range_ideleToClassH2 :
    (ideleToClassH2 K L).range = (classToMultiplicativeH3 K L).ker := by
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    (groupCohomology.mapShortComplex₃_exact (ideleShortComplex_shortExact K L) (i := 2) rfl)
  exact congrArg Submodule.toAddSubgroup h

/-- **On a cyclic layer every class of `H²(Gal(L/F), C_L)` lifts to the ideles.** For cyclic
`Gal(L/F)`, `H³(Gal(L/F), Lˣ) ≅ H¹(Gal(L/F), Lˣ)` by two-periodicity, and the latter vanishes by
Hilbert 90, so the obstruction `classToMultiplicativeH3` is zero. -/
theorem surjective_ideleToClassH2_of_isCyclic [IsCyclic L.Gal] :
    Function.Surjective (ideleToClassH2 K L) := by
  have : Subsingleton (L.H (unitsFormation K) 1) := subsingleton_h1_unitsFormation L
  have e : L.H (unitsFormation K) 3 ≅ L.H (unitsFormation K) 1 :=
    (L.tateHIsoH _ 3).symm ≪≫ Rep.FiniteCyclicGroup.periodicIso _ (3 : ℕ) (1 : ℕ) (by decide) ≪≫
      L.tateHIsoH _ 1
  have : Subsingleton (L.H (unitsFormation K) 3) := e.toLinearEquiv.toEquiv.subsingleton
  intro x
  have hx : x ∈ (classToMultiplicativeH3 K L).ker := Subsingleton.elim _ _
  rw [← range_ideleToClassH2] at hx
  exact hx

end TauCeti.ClassFieldTheory
