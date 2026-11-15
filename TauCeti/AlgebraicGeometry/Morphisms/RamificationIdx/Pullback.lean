/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationIdx.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus.Pullback
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
public import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint
public import TauCeti.RingTheory.RamificationInertia.BaseChange
public import TauCeti.RingTheory.RamificationInertia.Bijective

/-!
# Pointwise ramification indices under base change and closed-fibre comparison

This file relates `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt` to `ramificationLocus` and
studies its behaviour under open immersions, `Spec.map`, commutative squares, and base change along
an arbitrary field extension `L / k`:

* `ramificationIdxAt` equals `1` when the source stalk is a field or the stalk map is surjective,
  is invariant under postcomposition with morphisms surjective on stalks and precomposition with
  open immersions, and agrees on `Spec.map (algebraMap R S)` with `Ideal.ramificationIdx`.
* For a morphism `f` locally of finite type, `x ∉ f.ramificationLocus` iff `f.ramificationIdxAt x =
  1` and `κ(x) / κ(f x)` is separable
  (`notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable`). At a quasi-finite point
  over a perfect residue field `κ(f x)`, `x ∈ f.ramificationLocus ↔ f.ramificationIdxAt x ≠ 1`
  (`mem_ramificationLocus_iff_ramificationIdxAt_ne_one`).
* In any commutative square `gX ≫ f = f' ≫ gY` with `(gX.stalkMap x').hom.Flat` and vertical
  ramification indices `1`, `f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')` with no flatness
  assumption on `f` or `f'` (`ramificationIdxAt_eq_of_commSq_of_eq_one`).
* For a `k`-scheme `X` pulled back along an arbitrary field extension `L / k`, every point `x'` of
  `X'` over a point of `X` with separable residue field over `k` satisfies
  `gX.ramificationIdxAt x' = 1`
  (`ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField`),
  so for a `k`-morphism `f : X ⟶ Y` pulled back to `f' : X' ⟶ Y'`,
  `f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')` whenever `κ(gX x')` and `κ(f (gX x'))`
  are separable over `k` — in particular at closed points over a perfect field `k`.
* Over an algebraically closed field `k` (such as `AlgebraicClosure ℚ`), base change along an
  arbitrary field extension `L / k` (such as `ℂ / AlgebraicClosure ℚ`) induces a canonical
  bijection on closed fibres `{x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'}` preserving
  `ramificationIdxAt` (`fiberEquivOfIsAlgClosed`,
  `ramificationIdxAt_fiberEquivOfIsAlgClosed`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_specMap`
* `Scheme.Hom.notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable`,
  `AlgebraicGeometry.Scheme.Hom.mem_ramificationLocus_iff_ramificationIdxAt_ne_one`
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_commSq_of_eq_one`
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField`
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isSeparable_residueField`
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_eq_of_isPullback_of_isClosed`
* `AlgebraicGeometry.Scheme.Hom.fiberEquivOfIsAlgClosed`
* `AlgebraicGeometry.Scheme.Hom.ramificationIdxAt_fiberEquivOfIsAlgClosed`
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

section Basic

/-- If the stalk of `X` at `x` is a field, the ramification index of any morphism `f : X ⟶ Y` at
`x` is `1`. -/
theorem ramificationIdxAt_eq_one_of_isField {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    (hx : IsField (X.presheaf.stalk x)) : f.ramificationIdxAt x = 1 := by
  let := (f.stalkMap x).hom.toAlgebra
  let := hx.toField
  rw [ramificationIdxAt_def, isField_iff_maximalIdeal_eq.mp hx, Ideal.ramificationIdx_bot_eq_one]

/-- If `f.stalkMap x` is surjective, `f.ramificationIdxAt x = 1`. -/
theorem ramificationIdxAt_eq_one_of_surjective_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X}
    (hsurj : Function.Surjective (f.stalkMap x).hom) : f.ramificationIdxAt x = 1 := by
  let := (f.stalkMap x).hom.toAlgebra
  rw [ramificationIdxAt_def, ramificationIdx_maximalIdeal_eq_one_iff]
  exact Ideal.map_comap_of_surjective _ hsurj _

/-- A morphism surjective on stalks (such as an open or closed immersion) has ramification index `1`
at every point. -/
@[simp]
theorem ramificationIdxAt_eq_one_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : f.ramificationIdxAt x = 1 :=
  f.ramificationIdxAt_eq_one_of_surjective_stalkMap (SurjectiveOnStalks.stalkMap_surjective f x)

/-- Postcomposing `f` with a morphism `g` whose stalk map at `f x` is surjective leaves
`ramificationIdxAt` at `x` unchanged, with no flatness assumption on `f`. -/
theorem ramificationIdxAt_comp_of_surjective_stalkMap {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) (hsurj : Function.Surjective (g.stalkMap (f x)).hom) :
    (f ≫ g).ramificationIdxAt x = f.ramificationIdxAt x := by
  let RZ := Z.presheaf.stalk ((f ≫ g) x)
  let RY := Y.presheaf.stalk (f x)
  let RX := X.presheaf.stalk x
  let : Algebra RZ RY := (g.stalkMap (f x)).hom.toAlgebra
  let : Algebra RY RX := (f.stalkMap x).hom.toAlgebra
  let : Algebra RZ RX := ((f ≫ g).stalkMap x).hom.toAlgebra
  have : IsScalarTower RZ RY RX :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x))
  rw [ramificationIdxAt_def, ramificationIdxAt_def]
  exact (Ideal.ramificationIdx_eq_of_surjective (R := RZ) (S := RY) hsurj _).symm

/-- Postcomposing `f` with a morphism surjective on stalks (such as an open or closed immersion)
leaves `ramificationIdxAt` unchanged. -/
@[simp]
theorem ramificationIdxAt_comp_of_surjectiveOnStalks {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [SurjectiveOnStalks g] (x : X) :
    (f ≫ g).ramificationIdxAt x = f.ramificationIdxAt x :=
  ramificationIdxAt_comp_of_surjective_stalkMap f g x
    (SurjectiveOnStalks.stalkMap_surjective g (f x))

/-- Precomposing with an open immersion preserves `ramificationIdxAt`. -/
theorem ramificationIdxAt_isOpenImmersion_comp {X Y Z : Scheme.{u}} (ι : X ⟶ Y) [IsOpenImmersion ι]
    (f : Y ⟶ Z) (x : X) :
    (ι ≫ f).ramificationIdxAt x = f.ramificationIdxAt (ι x) := by
  simp

/-- In a commutative square `ι ≫ f' = h ≫ j` with open immersions `ι` and `j`,
`f'.ramificationIdxAt (ι q) = h.ramificationIdxAt q`. -/
theorem ramificationIdxAt_eq_of_isOpenImmersion_square {X₀ Y₀ X' Y' : Scheme.{u}} (ι : X₀ ⟶ X')
    (f' : X' ⟶ Y') (h : X₀ ⟶ Y₀) (j : Y₀ ⟶ Y') [IsOpenImmersion ι] [IsOpenImmersion j]
    (e : ι ≫ f' = h ≫ j) (q : X₀) :
    f'.ramificationIdxAt (ι q) = h.ramificationIdxAt q := by
  rw [← ramificationIdxAt_isOpenImmersion_comp ι f' q, e,
    ramificationIdxAt_comp_of_surjectiveOnStalks]

/-- On affine schemes, `ramificationIdxAt` of `Spec.map (algebraMap R S)` at a prime `q` of `S`
is `q.asIdeal.ramificationIdx R`. -/
@[simp]
theorem ramificationIdxAt_specMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : Spec (.of S)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).ramificationIdxAt q =
      q.asIdeal.ramificationIdx R := by
  have := q.isPrime
  let φ := CommRingCat.ofHom (algebraMap R S)
  let p := PrimeSpectrum.comap φ.hom q
  have : p.asIdeal.IsPrime := p.isPrime
  have : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let Rp := Localization.AtPrime p.asIdeal
  let Sq := Localization.AtPrime q.asIdeal
  let : Algebra Rp Sq := (Localization.localRingHom p.asIdeal q.asIdeal φ.hom rfl).toAlgebra
  have : IsScalarTower R Rp Sq :=
    .of_algebraMap_eq fun r ↦
      (Localization.localRingHom_to_map p.asIdeal q.asIdeal φ.hom rfl r).symm
  have : IsLocalHom (algebraMap Rp Sq) :=
    Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal φ.hom rfl
  let SR := (Spec (.of R)).presheaf.stalk ((Spec.map φ) q)
  let SS := (Spec (.of S)).presheaf.stalk q
  let ep : CommRingCat.of Rp ≅ SR := (AlgebraicGeometry.Spec.stalkIso (.of R) p).symm
  let eq : SS ≅ CommRingCat.of Sq := AlgebraicGeometry.Spec.stalkIso (.of S) q
  let : Algebra Rp SR := ep.hom.hom.toAlgebra
  let : Algebra SR SS := ((Spec.map φ).stalkMap q).hom.toAlgebra
  let : Algebra SR Sq := (((Spec.map φ).stalkMap q) ≫ eq.hom).hom.toAlgebra
  have hsq : ep.hom ≫ (Spec.map φ).stalkMap q ≫ eq.hom =
      CommRingCat.ofHom (algebraMap Rp Sq) :=
    (Iso.inv_comp_eq ep.symm).mpr
      ((Iso.comp_inv_eq eq).mp
        ((Category.assoc ep.symm.hom (CommRingCat.ofHom (algebraMap Rp Sq)) eq.inv).trans
          (localRingHom_comp_stalkIso φ q))).symm
  have : IsScalarTower Rp SR Sq := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsq).symm
  let algEq : SS ≃ₐ[SR] Sq :=
    AlgEquiv.ofRingEquiv (f := eq.commRingCatIsoToRingEquiv) fun _ ↦ rfl
  have : IsLocalHom algEq.toRingHom := ⟨fun a ha ↦ (isUnit_map_iff algEq a).mp ha⟩
  have hmax : (maximalIdeal SS).map algEq = maximalIdeal Sq := by
    change (maximalIdeal SS).map algEq.toRingHom = maximalIdeal Sq
    rw [← maximalIdeal_comap algEq.toRingHom]
    exact Ideal.map_comap_of_surjective algEq.toRingHom algEq.surjective (maximalIdeal Sq)
  have hep : Function.Surjective (algebraMap Rp SR) :=
    (ConcreteCategory.bijective_of_isIso ep.hom).surjective
  rw [ramificationIdxAt_def, ← Ideal.ramificationIdx_map_algEquiv algEq, hmax,
    Ideal.ramificationIdx_eq_of_surjective hep,
    Ideal.ramificationIdx_maximalIdeal_localization_of_liesOver p.asIdeal q.asIdeal]

end Basic

section RamificationLocus

/-- **Pointwise criterion for the ramification locus.** For a morphism `f : X ⟶ Y` locally of
finite type, `x ∉ f.ramificationLocus` iff `f.ramificationIdxAt x = 1` and the residue field
extension `κ(x) / κ(f x)` is separable. -/
theorem notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    x ∉ f.ramificationLocus ↔
      f.ramificationIdxAt x = 1 ∧
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Algebra.EssFiniteType R S :=
    RingHom.essFiniteType_algebraMap.mp (LocallyOfFiniteType.stalkMap f x)
  have hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S) ↔
      letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
    constructor <;> intro h <;>
    · convert! h
      refine Algebra.algebra_ext _ _ fun r ↦ ?_
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
      rfl
  rw [mem_ramificationLocus_iff, not_not, RingHom.FormallyUnramified,
    ← RingHom.algebraMap_toAlgebra (f.stalkMap x).hom,
    Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, hsep, ramificationIdxAt_def,
    ramificationIdx_maximalIdeal_eq_one_iff, Ideal.under, maximalIdeal_comap, and_comm]

/-- Outside the ramification locus of a locally finite-type morphism, the ramification index is
`1`. -/
theorem ramificationIdxAt_eq_one_of_notMem_ramificationLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {x : X} (hx : x ∉ f.ramificationLocus) :
    f.ramificationIdxAt x = 1 :=
  ((notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable f x).mp hx).1

/-- At a quasi-finite point of a locally finite-type morphism over a perfect residue field
`κ(f x)` (in particular in characteristic zero), `x` lies in `f.ramificationLocus` iff
`f.ramificationIdxAt x ≠ 1`. -/
theorem mem_ramificationLocus_iff_ramificationIdxAt_ne_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {x : X} (hqf : f.QuasiFiniteAt x)
    [PerfectField (Y.residueField (f x))] :
    x ∈ f.ramificationLocus ↔ f.ramificationIdxAt x ≠ 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) := hqf.finite_residueField
  have hsep : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := inferInstance
  rw [← not_iff_not, not_not,
    notMem_ramificationLocus_iff_ramificationIdxAt_eq_one_and_isSeparable]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hsep⟩⟩

end RamificationLocus

section CommSq

/-- **Comparison of `ramificationIdxAt` in a commutative square.** Suppose `gX ≫ f = f' ≫ gY`,
`gX.stalkMap x'` is flat, `gX.ramificationIdxAt x' = 1`, and `gY.ramificationIdxAt (f' x') = 1`.
Then `f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')`, with no flatness assumption on `f` or
`f'`. -/
theorem ramificationIdxAt_eq_of_commSq_of_eq_one {X Y X' Y' : Scheme.{u}} {gX : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y} (w : gX ≫ f = f' ≫ gY) (x' : X')
    (hflat : (gX.stalkMap x').hom.Flat) (hgX : gX.ramificationIdxAt x' = 1)
    (hgY : gY.ramificationIdxAt (f' x') = 1) :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  let R := Y.presheaf.stalk (f (gX x'))
  let R' := Y.presheaf.stalk (gY (f' x'))
  let S := Y'.presheaf.stalk (f' x')
  let A := X.presheaf.stalk (gX x')
  let B := X'.presheaf.stalk x'
  have hw : f (gX x') = gY (f' x') := by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  let eR : R ⟶ R' := (Y.presheaf.stalkCongr (.of_eq hw)).hom
  let : Algebra R R' := eR.hom.toAlgebra
  let : Algebra R' S := (gY.stalkMap (f' x')).hom.toAlgebra
  let : Algebra R S := (eR ≫ gY.stalkMap (f' x')).hom.toAlgebra
  let : Algebra R A := (f.stalkMap (gX x')).hom.toAlgebra
  let : Algebra A B := (gX.stalkMap x').hom.toAlgebra
  let : Algebra S B := (f'.stalkMap x').hom.toAlgebra
  let : Algebra R B := (f.stalkMap (gX x') ≫ gX.stalkMap x').hom.toAlgebra
  have hsq : f.stalkMap (gX x') ≫ gX.stalkMap x' =
      (eR ≫ gY.stalkMap (f' x')) ≫ f'.stalkMap x' := by
    rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ w x',
      Scheme.Hom.stalkMap_comp, Category.assoc]
    rfl
  have : IsScalarTower R R' S := .of_algebraMap_eq' rfl
  have : IsScalarTower R A B := .of_algebraMap_eq' rfl
  have : IsScalarTower R S B := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hsq)
  have : IsLocalHom (algebraMap S B) := inferInstanceAs (IsLocalHom (f'.stalkMap x').hom)
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (gX.stalkMap x').hom)
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  have heR : Function.Surjective (algebraMap R R') :=
    (ConcreteCategory.bijective_of_isIso eR).surjective
  rw [ramificationIdxAt_def] at hgX hgY
  have hRS : (maximalIdeal S).ramificationIdx R = 1 := by
    rw [← Ideal.ramificationIdx_eq_of_surjective (T := S) heR]
    exact hgY
  rw [ramificationIdxAt_def, ramificationIdxAt_def]
  exact Ideal.ramificationIdx_eq_of_isLocalHom_square (R := R) (S := S) (A := A) (B := B) hgX hRS

end CommSq

section FieldPullback

/-- At a closed point `x` of a scheme `X` locally of finite type over `Spec k`, the residue field
`κ(x)` is a finite (hence algebraic) extension of `k`. -/
theorem finite_residueField_of_isClosed {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))] {x : X}
    (hx : IsClosed {x}) : Module.Finite k (X.residueField x) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite (X.fromSpecResidueField x ≫ (X ↘ Spec (.of k))) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  rw [X.fromSpecResidueField_comp_over (k := k)] at hfin
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)

/-- **Vertical ramification index one under field extension.** Let `X'` be the pullback of a
`k`-scheme `X` along an arbitrary field extension `L / k` (`gX : X' ⟶ X`). At any point `x' : X'`
such that `κ(gX x')` is separable over `k`, `gX.ramificationIdxAt x' = 1` (with no finite-type
assumption on `X` or `L / k`). -/
theorem ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField {k L : Type u}
    [Field k] [Field L] [Algebra k L] {X X' : Scheme.{u}} [X.Over (Spec (.of k))]
    [X'.Over (Spec (.of L))] {gX : X' ⟶ X}
    (HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {x' : X'} (hsep : Algebra.IsSeparable k (X.residueField (gX x'))) :
    gX.ramificationIdxAt x' = 1 := by
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (gX x')) isOpen_univ
  let _ : Algebra k Γ(X, V) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ V le_top).hom.toAlgebra
  have hVover : hV.fromSpec ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, V))) := by
    rw [hV.fromSpec_comp_eq_SpecMap, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  have := hV.isOpenImmersion_fromSpec
  obtain ⟨ι, hι, -, h₂, hrange⟩ :=
    TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_of_isPullback HX
      (iY := 𝟙 (Spec (.of k))) (iY' := 𝟙 (Spec (.of L))) (iX := hV.fromSpec)
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hVover])
  have hx'ι : x' ∈ Set.range ι := by
    rw [hrange, hV.range_fromSpec]
    exact ⟨⟨X' ↘ Spec (.of L) <| x', rfl⟩, hxV⟩
  obtain ⟨q, rfl⟩ := hx'ι
  have := q.isPrime
  let B := L ⊗[k] Γ(X, V)
  let _ : Algebra Γ(X, V) B := Algebra.TensorProduct.rightAlgebra
  let φR := CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[k] B).toRingHom
  let p := Spec.map φR q
  have := p.isPrime
  have hgx : gX (ι q) = hV.fromSpec p := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : _ ⟶ X ↦ m q) h₂
  have hp : p.asIdeal = q.asIdeal.under Γ(X, V) :=
    (congrArg PrimeSpectrum.asIdeal (Spec.map_apply φR q)).trans
      (PrimeSpectrum.comap_asIdeal _ q)
  rw [hgx] at hsep
  let eRes : X.residueField (hV.fromSpec p) ≃ₐ[k] p.asIdeal.ResidueField :=
    hV.fromSpec.residueFieldAlgEquivOfIsOpenImmersion
      (CommRingCat.ofHom (algebraMap k Γ(X, V))) hVover.symm p
  have hsepP : Algebra.IsSeparable k p.asIdeal.ResidueField :=
    Algebra.IsSeparable.of_algHom _ _ eRes.symm.toAlgHom
  have : (q.asIdeal.under Γ(X, V)).IsPrime := Ideal.IsPrime.under _ _
  have hsepI : ∀ (I : Ideal Γ(X, V)) [I.IsPrime],
      p.asIdeal = I → Algebra.IsSeparable k I.ResidueField := by
    rintro I _ rfl
    convert hsepP
  rw [ramificationIdxAt_eq_of_isOpenImmersion_square ι gX _ hV.fromSpec h₂ q,
    ramificationIdxAt_specMap]
  exact Ideal.ramificationIdx_eq_one_of_isPushout_of_isSeparable k L q.asIdeal
    (hsepI (q.asIdeal.under Γ(X, V)) hp)

/-- Over a perfect field `k`, at any point `x'` of `X'` lying over a closed point of a
locally-finite-type `k`-scheme `X`, `gX.ramificationIdxAt x' = 1`. -/
theorem ramificationIdxAt_eq_one_of_isPullback_of_isClosed {k L : Type u} [Field k]
    [PerfectField k] [Field L] [Algebra k L] {X X' : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [X'.Over (Spec (.of L))] {gX : X' ⟶ X}
    (HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {x' : X'} (hx : IsClosed {gX x'}) :
    gX.ramificationIdxAt x' = 1 := by
  have : Module.Finite k (X.residueField (gX x')) := finite_residueField_of_isClosed hx
  exact ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField HX inferInstance

/-- **Horizontal ramification index invariance under field extension.** Let `f : X ⟶ Y` be a
`k`-morphism pulled back along an arbitrary field extension `L / k` to `f' : X' ⟶ Y'`. At any
point `x' : X'` such that both `κ(gX x')` and `κ(f (gX x'))` are separable over `k`,
`f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x')`, with no flatness assumption on `f`. -/
theorem ramificationIdxAt_eq_of_isPullback_of_isSeparable_residueField {k L : Type u}
    [Field k] [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {x' : X'} (hsepX : Algebra.IsSeparable k (X.residueField (gX x')))
    (hsepY : Algebra.IsSeparable k (Y.residueField (f (gX x')))) :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  have HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    simpa only [comp_over] using Hf.paste_vert HY
  have : Flat gX := MorphismProperty.of_isPullback (P := @Flat) HX.flip inferInstance
  have hw : gY (f' x') = f (gX x') := by
    rw [← Scheme.Hom.comp_apply, ← Hf.w, Scheme.Hom.comp_apply]
  refine ramificationIdxAt_eq_of_commSq_of_eq_one Hf.w x' (Flat.stalkMap gX x')
    (ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField HX hsepX) ?_
  refine ramificationIdxAt_eq_one_of_isPullback_of_isSeparable_residueField HY ?_
  rwa [hw]

/-- Over a perfect field `k` (in particular in characteristic zero), horizontal ramification
indices of locally-finite-type `k`-schemes are preserved under base change along any field
extension `L / k` at every point `x'` mapping to closed points of `X` and `Y`. -/
theorem ramificationIdxAt_eq_of_isPullback_of_isClosed {k L : Type u} [Field k] [PerfectField k]
    [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {x' : X'} (hx : IsClosed {gX x'}) (hy : IsClosed {f (gX x')}) :
    f'.ramificationIdxAt x' = f.ramificationIdxAt (gX x') := by
  have : Module.Finite k (X.residueField (gX x')) := finite_residueField_of_isClosed hx
  have : Module.Finite k (Y.residueField (f (gX x'))) := finite_residueField_of_isClosed hy
  exact ramificationIdxAt_eq_of_isPullback_of_isSeparable_residueField Hf HY
    inferInstance inferInstance

end FieldPullback

section AlgClosedFiber

/-- Over an algebraically closed field `k`, every closed point `x` of a locally-finite-type
`k`-scheme `X` has a unique preimage in the base change `X'` along any field extension `L / k`. -/
theorem existsUnique_preimage_of_isPullback_of_isAlgClosed {k L : Type u} [Field k]
    [IsAlgClosed k] [Field L] [Algebra k L] {X X' : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [X'.Over (Spec (.of L))] {gX : X' ⟶ X}
    (HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {x : X} (hx : IsClosed {x}) :
    ∃! x' : X', gX x' = x := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let s : Spec (.of k) ⟶ X := pointOfClosedPoint (X ↘ Spec (.of k)) x hx
  have hs : s ≫ (X ↘ Spec (.of k)) = 𝟙 _ := pointOfClosedPoint_comp (X ↘ Spec (.of k)) x hx
  have hw : (b ≫ s) ≫ (X ↘ Spec (.of k)) = 𝟙 _ ≫ b := by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
  let s' : Spec (.of L) ⟶ X' := HX.lift (b ≫ s) (𝟙 _) hw
  have hpre := TauCeti.AlgebraicGeometry.preimage_singleton_section_closedPoint_of_isPullback HX
    hs (HX.lift_snd (b ≫ s) (𝟙 _) hw) (HX.lift_fst (b ≫ s) (𝟙 _) hw)
  have hsx : s (closedPoint k) = x := pointOfClosedPoint_apply (X ↘ Spec (.of k)) x hx _
  rw [hsx] at hpre
  refine ⟨s' (closedPoint L), ?_, fun z hz ↦ ?_⟩
  · exact Set.mem_preimage.mp (hpre.symm ▸ Set.mem_singleton _)
  · exact Set.mem_singleton_iff.mp (hpre ▸ Set.mem_preimage.mpr hz)

/-- **Closed-fibre bijection under field extension from an algebraically closed field.** Let
`f : X ⟶ Y` be a morphism of locally-finite-type schemes over an algebraically closed field `k`
(such as `AlgebraicClosure ℚ`), pulled back along an arbitrary field extension `L / k` (such as
`ℂ / AlgebraicClosure ℚ`) to `f' : X' ⟶ Y'`. For any `y' : Y'` over a closed point `gY y'` of `Y`
whose fibre in `X` consists of closed points, `gX` restricts to a bijection
`{x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'}`. -/
noncomputable def fiberEquivOfIsAlgClosed {k L : Type u} [Field k] [IsAlgClosed k] [Field L]
    [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : IsClosed {gY y'}) (hfib : ∀ x : X, f x = gY y' → IsClosed {x}) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} := by
  have HX : IsPullback gX (X' ↘ Spec (.of L)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    simpa only [comp_over] using Hf.paste_vert HY
  refine Equiv.ofBijective (fun x' ↦ ⟨gX x'.1, by
      rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, x'.2]⟩) ⟨?_, ?_⟩
  · rintro ⟨x'₁, hx'₁⟩ ⟨x'₂, hx'₂⟩ h
    have heq : gX x'₁ = gX x'₂ := congrArg Subtype.val h
    have hxcl : IsClosed {gX x'₁} :=
      hfib (gX x'₁) (by rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, hx'₁])
    obtain ⟨_, -, hunique⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HX hxcl
    exact Subtype.ext ((hunique x'₁ rfl).trans (hunique x'₂ heq.symm).symm)
  · rintro ⟨x, hx⟩
    obtain ⟨x', hx', -⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HX (hfib x hx)
    obtain ⟨_, -, hyunique⟩ := existsUnique_preimage_of_isPullback_of_isAlgClosed HY hy
    have hfy' : f' x' = y' := by
      have hgy : gY (f' x') = gY y' := by
        rw [← Scheme.Hom.comp_apply, ← Hf.w, Scheme.Hom.comp_apply, hx', hx]
      exact (hyunique (f' x') hgy).trans (hyunique y' rfl).symm
    exact ⟨⟨x', hfy'⟩, Subtype.ext hx'⟩

/-- `fiberEquivOfIsAlgClosed` acts on underlying points via the projection `gX`. -/
@[simp]
theorem fiberEquivOfIsAlgClosed_coe {k L : Type u} [Field k] [IsAlgClosed k] [Field L]
    [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : IsClosed {gY y'}) (hfib : ∀ x : X, f x = gY y' → IsClosed {x})
    (x' : {x' : X' // f' x' = y'}) :
    (fiberEquivOfIsAlgClosed Hf HY y' hy hfib x').1 = gX x'.1 := by
  unfold fiberEquivOfIsAlgClosed
  rfl

/-- `fiberEquivOfIsAlgClosed` preserves pointwise ramification indices in arbitrary
characteristic. -/
theorem ramificationIdxAt_fiberEquivOfIsAlgClosed {k L : Type u} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : IsClosed {gY y'}) (hfib : ∀ x : X, f x = gY y' → IsClosed {x})
    (x' : {x' : X' // f' x' = y'}) :
    f'.ramificationIdxAt x'.1 =
      f.ramificationIdxAt (fiberEquivOfIsAlgClosed Hf HY y' hy hfib x').1 := by
  have hfgx : f (gX x'.1) = gY y' := by
    rw [← Scheme.Hom.comp_apply, Hf.w, Scheme.Hom.comp_apply, x'.2]
  exact ramificationIdxAt_eq_of_isPullback_of_isClosed Hf HY (hfib (gX x'.1) hfgx) (hfgx ▸ hy)

/-- For a locally quasi-finite morphism `f : X ⟶ Y` whose source is a Jacobson space, every point
of `X` lying over a closed point of `Y` is closed in `X`. -/
theorem isClosed_singleton_of_locallyQuasiFinite_of_isClosed {X Y : Scheme.{u}} [JacobsonSpace X]
    (f : X ⟶ Y) [LocallyQuasiFinite f] {x : X} (hy : IsClosed {f x}) :
    IsClosed {x} := by
  have hne : (closure ({x} : Set X) ∩ closedPoints X).Nonempty := by
    rw [← closure_nonempty_iff,
      JacobsonSpace.closure_inter_closedPoints_eq_closure isClosed_closure.isLocallyClosed,
      closure_closure, closure_nonempty_iff]
    exact ⟨x, rfl⟩
  obtain ⟨z, hzx, hzcl⟩ := hne
  have hspec : x ⤳ z := specializes_iff_mem_closure.mpr hzx
  have hfz : f z = f x := Set.mem_singleton_iff.mp ((hspec.map f.continuous).mem_closed hy rfl)
  have hzx_eq : x = z :=
    (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes hspec rfl hfz
  exact hzx_eq ▸ hzcl

/-- Specialization of `fiberEquivOfIsAlgClosed` to locally quasi-finite morphisms (such as finite
morphisms), where closedness of points in closed fibres is automatic. -/
noncomputable def fiberEquivOfIsAlgClosedOfLocallyQuasiFinite {k L : Type u} [Field k]
    [IsAlgClosed k] [Field L] [Algebra k L] {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [X'.Over (Spec (.of L))] [Y'.Over (Spec (.of L))]
    {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    [f.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of L))] [LocallyQuasiFinite f]
    (Hf : IsPullback gX f' f gY)
    (HY : IsPullback gY (Y' ↘ Spec (.of L)) (Y ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (y' : Y') (hy : IsClosed {gY y'}) :
    {x' : X' // f' x' = y'} ≃ {x : X // f x = gY y'} :=
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of k))
  fiberEquivOfIsAlgClosed Hf HY y' hy fun _ hx ↦
    isClosed_singleton_of_locallyQuasiFinite_of_isClosed f (hx ▸ hy)

end AlgClosedFiber

end AlgebraicGeometry.Scheme.Hom
