/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Restrict
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Hom
public import TauCeti.LinearAlgebra.RootSystem.EquivComp

/-!
# Dual isogeny lattices and lattice-preserving automorphisms of root pairings

Let `P` be a root pairing over a faithful `R`-algebra `S` on modules `M` and `N`. An `R`-submodule
pair `(X₀, Y₀)` in `M × N` determines `P.latticeAut X₀ Y₀ : Subgroup P.Aut`, the automorphisms
stabilizing `X₀` under `g.weightEquiv` and `Y₀` under `g.coweightEquiv.symm`.

When `X₀` contains all roots, `Y₀` contains all coroots, and `P.toLinearMap` restricts on `X₀ × Y₀`
to a perfect `R`-pairing (`P.IsDualLatticePair X₀ Y₀`), `P` restricts to an `R`-root pairing
`hXY.restrict : RootPairing ι R X₀ Y₀` with `P.weylGroup ≤ P.latticeAut X₀ Y₀` and a restriction
homomorphism `hXY.restrictAutHom : P.latticeAut X₀ Y₀ →* hXY.restrict.Aut`.

When `X₀` and `Y₀` are finite free `R`-lattices satisfying `IsBaseChange S X₀.subtype` and
`IsBaseChange S Y₀.subtype` (e.g. free full lattices over an integral domain in its fraction field,
or the unit-tensor lattices `1 ⊗ X` and `1 ⊗ Y` in `D.baseChange S`), scalar extension and lattice
restriction are mutually inverse (`hXY.autMulEquiv hX hY : hXY.restrict.Aut ≃* P.latticeAut X₀ Y₀`).

## Main definitions

* `RootPairing.latticeAut`: the subgroup of `P.Aut` preserving `X₀` under `weightEquiv` and `Y₀`
  under `coweightEquiv.symm`.
* `RootPairing.IsDualLatticePair` and `RootPairing.IsDualLatticePair.restrict`: dual `R`-lattice
  pairs and the restricted `R`-root pairing on `(X₀, Y₀)`.
* `RootPairing.IsDualLatticePair.restrictAutHom`, `RootPairing.IsDualLatticePair.baseChangeEquiv`,
  `RootPairing.IsDualLatticePair.extendAutHom`, and `RootPairing.IsDualLatticePair.autMulEquiv`:
  restriction and scalar extension of automorphisms and `hXY.restrict.Aut ≃* P.latticeAut X₀ Y₀`.
* `RootPairing.unitTmulRootPairingEquiv` and `RootPairing.autMulEquivLatticeAutBaseChange`:
  comparison of `D` with the unit-tensor lattices in `D.baseChange S`.

## Main results

* `RootPairing.mem_latticeAut_iff` and `RootPairing.mem_latticeAut_iff_forall`: setwise and
  elementwise characterizations of `P.latticeAut X₀ Y₀`.
* `RootPairing.IsDualLatticePair.weylGroup_le_latticeAut`: the Weyl group stabilizes every dual
  lattice pair.
* `RootPairing.IsDualLatticePair.restrictAutHom_extendAutHom` and
  `RootPairing.IsDualLatticePair.extendAutHom_restrictAutHom`: scalar extension and restriction of
  automorphisms are mutually inverse.
* `RootPairing.isDualLatticePair_range_mk_one` and `RootPairing.range_autBaseChangeHom`: the
  unit-tensor submodules in `D.baseChange S` form a dual lattice pair whose stabilizer is the exact
  range of `D.autBaseChangeHom S`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7,
  and 7.4.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C,
  C.43 and C.51.
-/

public section

open Function Module Set TensorProduct

namespace RootPairing

section LatticeAut

variable {ι R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module S M] [Module R M]
  [AddCommGroup N] [Module S N] [Module R N]

open Pointwise in
/-- **The lattice-preserving automorphism subgroup** for submodules `X₀ ≤ M` and `Y₀ ≤ N`: the
automorphisms `g : P.Aut` satisfying `g.weightEquiv '' X₀ = X₀` and
`g.coweightEquiv.symm '' Y₀ = Y₀`. It is the intersection of the inverse images of the setwise
stabilizers of `X₀` and `Y₀` under the forward weight and coweight representations. -/
noncomputable def latticeAut (P : RootPairing ι S M N)
    (X₀ : Submodule R M) (Y₀ : Submodule R N) : Subgroup P.Aut :=
  (MulAction.stabilizer (M ≃ₗ[S] M) (X₀ : Set M)).comap (Equiv.weightHom P) ⊓
    (MulAction.stabilizer (N ≃ₗ[S] N) (Y₀ : Set N)).comap (Equiv.forwardCoweightHom P)

variable {P : RootPairing ι S M N} {X₀ : Submodule R M} {Y₀ : Submodule R N}

/-- An automorphism belongs to `P.latticeAut X₀ Y₀` precisely when its forward weight and coweight
equivalences map `X₀` and `Y₀` onto themselves. -/
@[simp]
theorem mem_latticeAut_iff {g : P.Aut} :
    g ∈ P.latticeAut X₀ Y₀ ↔
      g.weightEquiv '' (X₀ : Set M) = X₀ ∧ g.coweightEquiv.symm '' (Y₀ : Set N) = Y₀ := by
  open Pointwise in
  simp only [latticeAut, Subgroup.mem_inf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
    ← Set.image_smul, Equiv.weightHom_apply, Equiv.forwardCoweightHom_apply]
  rfl

/-- Elementwise characterization of membership in `P.latticeAut X₀ Y₀`. -/
theorem mem_latticeAut_iff_forall {g : P.Aut} :
    g ∈ P.latticeAut X₀ Y₀ ↔
      (∀ x, g.weightEquiv x ∈ X₀ ↔ x ∈ X₀) ∧
        (∀ y, g.coweightEquiv.symm y ∈ Y₀ ↔ y ∈ Y₀) := by
  rw [mem_latticeAut_iff, ← Set.eq_preimage_iff_image_eq g.weightEquiv.bijective,
    ← Set.eq_preimage_iff_image_eq g.coweightEquiv.symm.bijective, Set.ext_iff, Set.ext_iff]
  exact and_congr (forall_congr' fun _ ↦ iff_comm) (forall_congr' fun _ ↦ iff_comm)

/-- A lattice-preserving automorphism preserves `X₀` under `weightEquiv`. -/
theorem weightEquiv_mem_iff_of_mem_latticeAut {g : P.Aut} (hg : g ∈ P.latticeAut X₀ Y₀) (x : M) :
    g.weightEquiv x ∈ X₀ ↔ x ∈ X₀ :=
  (mem_latticeAut_iff_forall.mp hg).1 x

/-- A lattice-preserving automorphism preserves `X₀` under `weightEquiv.symm`. -/
theorem weightEquiv_symm_mem_iff_of_mem_latticeAut {g : P.Aut}
    (hg : g ∈ P.latticeAut X₀ Y₀) (x : M) : g.weightEquiv.symm x ∈ X₀ ↔ x ∈ X₀ := by
  simpa using (weightEquiv_mem_iff_of_mem_latticeAut hg (g.weightEquiv.symm x)).symm

/-- A lattice-preserving automorphism preserves `Y₀` under `coweightEquiv.symm`. -/
theorem coweightEquiv_symm_mem_iff_of_mem_latticeAut {g : P.Aut}
    (hg : g ∈ P.latticeAut X₀ Y₀) (y : N) : g.coweightEquiv.symm y ∈ Y₀ ↔ y ∈ Y₀ :=
  (mem_latticeAut_iff_forall.mp hg).2 y

/-- A lattice-preserving automorphism also preserves `Y₀` under the contravariant map
`coweightEquiv`, since `coweightEquiv` is the inverse of `coweightEquiv.symm`. -/
theorem coweightEquiv_mem_iff_of_mem_latticeAut {g : P.Aut}
    (hg : g ∈ P.latticeAut X₀ Y₀) (y : N) : g.coweightEquiv y ∈ Y₀ ↔ y ∈ Y₀ := by
  simpa using (coweightEquiv_symm_mem_iff_of_mem_latticeAut hg (g.coweightEquiv y)).symm

/-- `RootPairing.Equiv.autFlip` carries `P.latticeAut X₀ Y₀` onto `P.flip.latticeAut Y₀ X₀`. -/
theorem autFlip_mem_latticeAut_iff {g : P.Aut} :
    Equiv.autFlip P g ∈ P.flip.latticeAut Y₀ X₀ ↔ g ∈ P.latticeAut X₀ Y₀ := by
  simp only [mem_latticeAut_iff, Equiv.weightEquiv_autFlip, Equiv.coweightEquiv_autFlip,
    LinearEquiv.symm_symm, and_comm]

end LatticeAut

section DualLatticePair

variable {ι R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- **`(X₀, Y₀)` is a pair of dual `R`-lattices for `P`** when `X₀` contains all roots of `P`,
`Y₀` contains all coroots of `P`, the ambient pairing takes values in `algebraMap R S` on
`X₀ × Y₀`, and the restricted `R`-bilinear map on `X₀ × Y₀` is a perfect `R`-pairing. -/
structure IsDualLatticePair (P : RootPairing ι S M N)
    (X₀ : Submodule R M) (Y₀ : Submodule R N) : Prop where
  /-- Every root of `P` lies in `X₀`. -/
  range_root_subset : range P.root ⊆ X₀
  /-- Every coroot of `P` lies in `Y₀`. -/
  range_coroot_subset : range P.coroot ⊆ Y₀
  /-- The pairing of `P` on `X₀ × Y₀` takes values in the image of `algebraMap R S`. -/
  pairing_mem_range : ∀ x ∈ X₀, ∀ y ∈ Y₀, P.toLinearMap x y ∈ (algebraMap R S).range
  /-- The restricted `R`-bilinear pairing on `X₀ × Y₀` is a perfect `R`-pairing. -/
  isPerfPair :
    (LinearMap.restrictScalarsRange₂ X₀.subtype Y₀.subtype (Algebra.linearMap R S)
      (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
      fun x y ↦ pairing_mem_range x x.2 y y.2).IsPerfPair

namespace IsDualLatticePair

variable {P : RootPairing ι S M N} {X₀ : Submodule R M} {Y₀ : Submodule R N}
  (hXY : P.IsDualLatticePair X₀ Y₀)

include hXY in
/-- Every root of `P` belongs to `X₀`. -/
theorem root_mem (i : ι) : P.root i ∈ X₀ := hXY.range_root_subset (mem_range_self i)

include hXY in
/-- Every coroot of `P` belongs to `Y₀`. -/
theorem coroot_mem (i : ι) : P.coroot i ∈ Y₀ := hXY.range_coroot_subset (mem_range_self i)

include hXY in
/-- Swapping `X₀` and `Y₀` gives a dual lattice pair for `P.flip`. -/
theorem flip : P.flip.IsDualLatticePair Y₀ X₀ where
  range_root_subset := hXY.range_coroot_subset
  range_coroot_subset := hXY.range_root_subset
  pairing_mem_range y hy x hx := hXY.pairing_mem_range x hx y hy
  isPerfPair := by
    let p₀ := LinearMap.restrictScalarsRange₂ X₀.subtype Y₀.subtype (Algebra.linearMap R S)
      (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
      fun x y ↦ hXY.pairing_mem_range x x.2 y y.2
    let _ : p₀.flip.IsPerfPair := hXY.isPerfPair.flip
    refine LinearMap.IsPerfPair.congr (p := p₀.flip) (LinearEquiv.refl R Y₀)
      (LinearEquiv.refl R X₀) _ ?_
    ext y x; apply FaithfulSMul.algebraMap_injective R S
    exact (LinearMap.restrictScalarsRange₂_apply Y₀.subtype X₀.subtype (Algebra.linearMap R S)
      (FaithfulSMul.algebraMap_injective R S) P.flip.toLinearMap
      (fun y x ↦ hXY.pairing_mem_range x x.2 y y.2) y x).trans
      (LinearMap.restrictScalarsRange₂_apply X₀.subtype Y₀.subtype (Algebra.linearMap R S)
        (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
        (fun x y ↦ hXY.pairing_mem_range x x.2 y y.2) x y).symm

/-- **Restriction of a root pairing to dual `R`-sublattices `(X₀, Y₀)`.** -/
noncomputable def restrict : RootPairing ι R X₀ Y₀ :=
  let B := LinearMap.restrictScalarsRange₂ X₀.subtype Y₀.subtype (Algebra.linearMap R S)
    (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
    fun x y ↦ hXY.pairing_mem_range x x.2 y y.2
  have hB (x : X₀) (y : Y₀) : algebraMap R S (B x y) = P.toLinearMap x y :=
    LinearMap.restrictScalarsRange₂_apply X₀.subtype Y₀.subtype (Algebra.linearMap R S)
      (FaithfulSMul.algebraMap_injective R S) P.toLinearMap _ x y
  { toLinearMap := B
    isPerfPair_toLinearMap := hXY.isPerfPair
    root := ⟨fun i ↦ ⟨P.root i, hXY.root_mem i⟩,
      fun _ _ h ↦ P.root.injective (congrArg Subtype.val h)⟩
    coroot := ⟨fun i ↦ ⟨P.coroot i, hXY.coroot_mem i⟩,
      fun _ _ h ↦ P.coroot.injective (congrArg Subtype.val h)⟩
    root_coroot_two i := FaithfulSMul.algebraMap_injective R S <|
      (hB _ _).trans <| (P.root_coroot_two i).trans (map_ofNat (algebraMap R S) 2).symm
    reflectionPerm := P.reflectionPerm
    reflectionPerm_root i j := Subtype.ext <| by
      change P.root j - B ⟨P.root j, hXY.root_mem j⟩ ⟨P.coroot i, hXY.coroot_mem i⟩ • P.root i =
        P.root (P.reflectionPerm i j)
      rw [← algebraMap_smul S, hB]; exact P.reflectionPerm_root i j
    reflectionPerm_coroot i j := Subtype.ext <| by
      change P.coroot j -
          B ⟨P.root i, hXY.root_mem i⟩ ⟨P.coroot j, hXY.coroot_mem j⟩ • P.coroot i =
        P.coroot (P.reflectionPerm i j)
      rw [← algebraMap_smul S, hB]; exact P.reflectionPerm_coroot i j }

/-- Coercing a restricted root back to `M` recovers the ambient root. -/
@[simp]
theorem restrict_coe_root (i : ι) : (hXY.restrict.root i : M) = P.root i :=
  (rfl)

/-- Coercing a restricted coroot back to `N` recovers the ambient coroot. -/
@[simp]
theorem restrict_coe_coroot (i : ι) : (hXY.restrict.coroot i : N) = P.coroot i :=
  (rfl)

/-- The restricted pairing agrees with the ambient pairing after `algebraMap R S`. -/
@[simp]
theorem algebraMap_restrict_toLinearMap (x : X₀) (y : Y₀) :
    algebraMap R S (hXY.restrict.toLinearMap x y) = P.toLinearMap x y :=
  LinearMap.restrictScalarsRange₂_apply X₀.subtype Y₀.subtype (Algebra.linearMap R S)
    (FaithfulSMul.algebraMap_injective R S) P.toLinearMap _ x y

/-- The root-coroot pairings of `hXY.restrict` map to those of `P` under `algebraMap R S`. -/
@[simp]
theorem algebraMap_restrict_pairing (i j : ι) :
    algebraMap R S (hXY.restrict.pairing i j) = P.pairing i j := by
  rw [← hXY.restrict.root_coroot_eq_pairing, hXY.algebraMap_restrict_toLinearMap,
    hXY.restrict_coe_root, hXY.restrict_coe_coroot, P.root_coroot_eq_pairing]

/-- Lattice restriction leaves `reflectionPerm` unchanged. -/
@[simp]
theorem restrict_reflectionPerm : hXY.restrict.reflectionPerm = P.reflectionPerm :=
  (rfl)

/-- Evaluating a restricted coroot functional and mapping to `S` agrees with `P.coroot'`. -/
theorem algebraMap_restrict_coroot' (i : ι) (x : X₀) :
    algebraMap R S (hXY.restrict.coroot' i x) = P.coroot' i x := by
  simp [coroot']

/-- Evaluating a restricted root functional and mapping to `S` agrees with `P.root'`. -/
theorem algebraMap_restrict_root' (i : ι) (y : Y₀) :
    algebraMap R S (hXY.restrict.root' i y) = P.root' i y := by
  simp [root']

/-- Restricted reflections act as restrictions of the ambient reflections. -/
@[simp]
theorem restrict_coe_reflection (i : ι) (x : X₀) :
    (hXY.restrict.reflection i x : M) = P.reflection i x := by
  simp [reflection_apply, ← algebraMap_smul S]

/-- Restricted coreflections act as restrictions of the ambient coreflections. -/
@[simp]
theorem restrict_coe_coreflection (i : ι) (y : Y₀) :
    (hXY.restrict.coreflection i y : N) = P.coreflection i y := by
  simp [coreflection_apply, ← algebraMap_smul S]

/-- If `P` takes values in `T` along a scalar tower `T → R → S`, then so does `hXY.restrict`. -/
theorem isValuedIn_restrict (T : Type*) [CommRing T] [Algebra T R] [Algebra T S]
    [IsScalarTower T R S] [P.IsValuedIn T] : hXY.restrict.IsValuedIn T where
  exists_value i j := by
    obtain ⟨t, ht⟩ := P.exists_value (S := T) i j
    refine ⟨t, FaithfulSMul.algebraMap_injective R S ?_⟩
    rw [← IsScalarTower.algebraMap_apply T R S, ht, hXY.algebraMap_restrict_pairing]

/-- Restriction preserves `T`-valued pairings (in particular Cartan integers when `T = ℤ`). -/
@[simp]
theorem restrict_pairingIn (T : Type*) [CommRing T] [Algebra T R] [Algebra T S]
    [IsScalarTower T R S] [FaithfulSMul T S] [P.IsValuedIn T] (i j : ι) :
    letI := hXY.isValuedIn_restrict T
    hXY.restrict.pairingIn T i j = P.pairingIn T i j := by
  let _ := hXY.isValuedIn_restrict T
  apply FaithfulSMul.algebraMap_injective T S
  rw [algebraMap_pairingIn, IsScalarTower.algebraMap_apply T R S, algebraMap_pairingIn,
    hXY.algebraMap_restrict_pairing]

/-- Restriction of a crystallographic root pairing along a faithful algebra is crystallographic. -/
theorem isCrystallographic_restrict [P.IsCrystallographic] : hXY.restrict.IsCrystallographic :=
  hXY.isValuedIn_restrict ℤ

/-- Restriction of a reduced root pairing along a faithful algebra is reduced. -/
theorem isReduced_restrict [P.IsReduced] : hXY.restrict.IsReduced where
  eq_or_eq_neg i j h := by
    have hS : ¬ LinearIndependent S ![P.root i, P.root j] := fun hli ↦ h <| by
      have hliR : LinearIndependent R ![P.root i, P.root j] := hli.restrict_scalars <| by
        simpa only [← Algebra.algebraMap_eq_smul_one] using FaithfulSMul.algebraMap_injective R S
      rw [show ![P.root i, P.root j] = X₀.subtype ∘ ![hXY.restrict.root i, hXY.restrict.root j] by
        ext k; fin_cases k <;> rfl] at hliR
      exact hliR.of_comp
    exact (IsReduced.eq_or_eq_neg (P := P) i j hS).imp Subtype.ext Subtype.ext

include hXY in
/-- Every root reflection of `P` stabilizes both lattices of a dual lattice pair. -/
theorem reflection_mem_latticeAut (i : ι) : Equiv.reflection P i ∈ P.latticeAut X₀ Y₀ := by
  have hsymm : (Equiv.reflection P i).coweightEquiv.symm = P.coreflection i :=
    (Equiv.forwardCoweightHom_apply _).symm.trans (Equiv.forwardCoweightHom_reflection P i)
  rw [mem_latticeAut_iff, Equiv.reflection_weightEquiv, hsymm,
    show (X₀ : Set M) = range X₀.subtype by ext; simp,
    show (Y₀ : Set N) = range Y₀.subtype by ext; simp, ← range_comp, ← range_comp]
  exact ⟨(congrArg range (funext (hXY.restrict_coe_reflection i)).symm).trans <|
      (hXY.restrict.reflection i).surjective.range_comp _,
    (congrArg range (funext (hXY.restrict_coe_coreflection i)).symm).trans <|
      (hXY.restrict.coreflection i).surjective.range_comp _⟩

include hXY in
/-- **The Weyl group of `P` is contained in `P.latticeAut X₀ Y₀`.** -/
theorem weylGroup_le_latticeAut : P.weylGroup ≤ P.latticeAut X₀ Y₀ :=
  (Subgroup.closure_le _).mpr <| range_subset_iff.mpr hXY.reflection_mem_latticeAut

/-- **Restriction of a lattice-preserving automorphism** to an automorphism of `hXY.restrict`. -/
noncomputable def restrictAut (g : P.latticeAut X₀ Y₀) : hXY.restrict.Aut :=
  let eX : X₀ ≃ₗ[R] X₀ :=
    { toFun x := ⟨(g : P.Aut).weightEquiv x,
        (weightEquiv_mem_iff_of_mem_latticeAut g.2 x).mpr x.2⟩
      invFun x := ⟨(g : P.Aut).weightEquiv.symm x,
        (weightEquiv_symm_mem_iff_of_mem_latticeAut g.2 x).mpr x.2⟩
      left_inv x := Subtype.ext ((g : P.Aut).weightEquiv.symm_apply_apply x)
      right_inv x := Subtype.ext ((g : P.Aut).weightEquiv.apply_symm_apply x)
      map_add' x y := Subtype.ext (map_add (g : P.Aut).weightEquiv (x : M) (y : M))
      map_smul' r x := Subtype.ext (by simp) }
  let eY : Y₀ ≃ₗ[R] Y₀ :=
    { toFun y := ⟨(g : P.Aut).coweightEquiv y,
        (coweightEquiv_mem_iff_of_mem_latticeAut g.2 y).mpr y.2⟩
      invFun y := ⟨(g : P.Aut).coweightEquiv.symm y,
        (coweightEquiv_symm_mem_iff_of_mem_latticeAut g.2 y).mpr y.2⟩
      left_inv y := Subtype.ext ((g : P.Aut).coweightEquiv.symm_apply_apply y)
      right_inv y := Subtype.ext ((g : P.Aut).coweightEquiv.apply_symm_apply y)
      map_add' x y := Subtype.ext (map_add (g : P.Aut).coweightEquiv (x : N) (y : N))
      map_smul' r y := Subtype.ext (by simp) }
  { weightMap := eX.toLinearMap
    coweightMap := eY.toLinearMap
    indexEquiv := (g : P.Aut).indexEquiv
    weight_coweight_transpose := by
      ext y x; apply FaithfulSMul.algebraMap_injective R S
      simpa [eX, eY] using (g : P.Aut).toLinearMap_weightEquiv (x : M) (y : N)
    root_weightMap := by
      ext i
      simp only [LinearEquiv.coe_coe, comp_apply, restrict_coe_root, Equiv.root_indexEquiv_eq_smul]
      rfl
    coroot_coweightMap := by ext i; simpa [eY] using (g : P.Aut).coroot_coweightMap_apply P P i
    bijective_weightMap := eX.bijective
    bijective_coweightMap := eY.bijective }

/-- **Restriction of lattice-preserving automorphisms**, as a group homomorphism
`P.latticeAut X₀ Y₀ →* hXY.restrict.Aut`. -/
noncomputable def restrictAutHom : P.latticeAut X₀ Y₀ →* hXY.restrict.Aut where
  toFun := hXY.restrictAut
  map_one' := Equiv.weightHom_injective _ <| LinearEquiv.ext fun _ ↦ rfl
  map_mul' _ _ := Equiv.weightHom_injective _ <| LinearEquiv.ext fun _ ↦ rfl

/-- Coercing the restricted weight action back to `M` agrees with the ambient weight action. -/
theorem coe_restrictAutHom_weightEquiv (g : P.latticeAut X₀ Y₀) (x : X₀) :
    ((hXY.restrictAutHom g).weightEquiv x : M) = (g : P.Aut).weightEquiv x :=
  (rfl)

/-- Coercing the restricted weight SMul back to `M` agrees with the ambient SMul. -/
@[simp]
theorem coe_restrictAutHom_smul (g : P.latticeAut X₀ Y₀) (x : X₀) :
    ((hXY.restrictAutHom g • x : X₀) : M) = (g : P.Aut) • (x : M) :=
  (rfl)

/-- Coercing the restricted forward coweight action back to `N` agrees with the ambient forward
coweight action. -/
@[simp]
theorem coe_restrictAutHom_coweightEquiv_symm (g : P.latticeAut X₀ Y₀) (y : Y₀) :
    ((hXY.restrictAutHom g).coweightEquiv.symm y : N) = (g : P.Aut).coweightEquiv.symm y := by
  apply (g : P.Aut).coweightEquiv.injective
  have h : ((hXY.restrictAutHom g).coweightEquiv
      ((hXY.restrictAutHom g).coweightEquiv.symm y) : N) =
      (g : P.Aut).coweightEquiv ((hXY.restrictAutHom g).coweightEquiv.symm y : N) := rfl
  rw [LinearEquiv.apply_symm_apply, ← h, LinearEquiv.apply_symm_apply]

/-- Restriction of automorphisms preserves the root-index permutation. -/
@[simp]
theorem restrictAutHom_indexEquiv (g : P.latticeAut X₀ Y₀) :
    (hXY.restrictAutHom g).indexEquiv = (g : P.Aut).indexEquiv :=
  (rfl)

/-- Restriction sends each ambient root reflection to the corresponding reflection of
`hXY.restrict`. -/
@[simp]
theorem restrictAutHom_reflection (i : ι) :
    hXY.restrictAutHom ⟨Equiv.reflection P i, hXY.reflection_mem_latticeAut i⟩ =
      Equiv.reflection hXY.restrict i :=
  Equiv.weightHom_injective _ <|
    LinearEquiv.ext fun x ↦ Subtype.ext (hXY.restrict_coe_reflection i x).symm

end IsDualLatticePair

end DualLatticePair

section IsBaseChange

variable {ι R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

namespace IsDualLatticePair

variable {P : RootPairing ι S M N} {X₀ : Submodule R M} {Y₀ : Submodule R N}
  (hXY : P.IsDualLatticePair X₀ Y₀) [Free R Y₀] [Module.Finite R Y₀]
  (hX : IsBaseChange S X₀.subtype) (hY : IsBaseChange S Y₀.subtype)

/-- **Scalar extension of `hXY.restrict` is canonically equivalent to `P`** when the inclusions of
`X₀` and `Y₀` exhibit `M` and `N` as base changes along `R → S`. -/
noncomputable def baseChangeEquiv : (hXY.restrict.baseChange S).Equiv P where
  weightMap := hX.equiv.toLinearMap
  coweightMap := hY.equiv.symm.toLinearMap
  indexEquiv := _root_.Equiv.refl ι
  weight_coweight_transpose := by
    have hcomp :
        (hX.equiv.toLinearMap.dualMap ∘ₗ P.flip.toPerfPair.toLinearMap) ∘ₗ hY.equiv.toLinearMap =
          ((hXY.restrict.baseChange S).flip.toPerfPair.toLinearMap ∘ₗ
            hY.equiv.symm.toLinearMap) ∘ₗ hY.equiv.toLinearMap := by
      refine AlgebraTensorModule.ext fun b y ↦ AlgebraTensorModule.ext fun a x ↦ ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      simp [hX.equiv_tmul, hY.equiv_tmul]; ring
    exact LinearMap.ext fun n ↦ by simpa using congr($hcomp (hY.equiv.symm n))
  root_weightMap := by ext i; simp [hX.equiv_tmul]
  coroot_coweightMap := by ext i; simpa using hY.equiv_symm_apply (hXY.restrict.coroot i)
  bijective_weightMap := hX.equiv.bijective
  bijective_coweightMap := hY.equiv.symm.bijective

/-- The weight equivalence of `hXY.baseChangeEquiv hX hY` is `hX.equiv`. -/
@[simp]
theorem baseChangeEquiv_weightEquiv : (hXY.baseChangeEquiv hX hY).weightEquiv = hX.equiv :=
  LinearEquiv.toLinearMap_injective rfl

/-- The forward coweight equivalence of `hXY.baseChangeEquiv hX hY` is `hY.equiv`. -/
@[simp]
theorem baseChangeEquiv_coweightEquiv_symm :
    (hXY.baseChangeEquiv hX hY).coweightEquiv.symm = hY.equiv := by
  have h : (hXY.baseChangeEquiv hX hY).coweightEquiv = hY.equiv.symm :=
    LinearEquiv.toLinearMap_injective rfl
  rw [h, LinearEquiv.symm_symm]

/-- `hXY.baseChangeEquiv hX hY` acts as the identity on root indices. -/
@[simp]
theorem baseChangeEquiv_indexEquiv :
    (hXY.baseChangeEquiv hX hY).indexEquiv = _root_.Equiv.refl ι :=
  (rfl)

private theorem autCongr_autBaseChangeHom_weightEquiv_coe (u : hXY.restrict.Aut) (x : X₀) :
    ((hXY.baseChangeEquiv hX hY).autCongr (hXY.restrict.autBaseChangeHom S u)).weightEquiv x =
      u.weightEquiv x := by
  have h := (hXY.baseChangeEquiv hX hY).autCongr_smul
    (hXY.restrict.autBaseChangeHom S u) (1 ⊗ₜ[R] x)
  rwa [hXY.restrict.autBaseChangeHom_smul_tmul, baseChangeEquiv_weightEquiv,
    hX.equiv_tmul, hX.equiv_tmul, one_smul, one_smul] at h

private theorem autCongr_autBaseChangeHom_coweightEquiv_symm_coe
    (u : hXY.restrict.Aut) (y : Y₀) :
    ((hXY.baseChangeEquiv hX hY).autCongr
      (hXY.restrict.autBaseChangeHom S u)).coweightEquiv.symm y = u.coweightEquiv.symm y := by
  let e := hXY.baseChangeEquiv hX hY
  let g := hXY.restrict.autBaseChangeHom S u
  have h : (e.autCongr g).coweightEquiv.symm (e.coweightEquiv.symm (1 ⊗ₜ[R] y)) =
      e.coweightEquiv.symm (g.coweightEquiv.symm (1 ⊗ₜ[R] y)) :=
    (e.autCongr g).coweightEquiv.injective <| by
      rw [LinearEquiv.apply_symm_apply, e.coweightEquiv_autCongr_apply,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rwa [hXY.restrict.autBaseChangeHom_coweightEquiv_symm_tmul,
    baseChangeEquiv_coweightEquiv_symm, hY.equiv_tmul, hY.equiv_tmul, one_smul, one_smul] at h

include hX hY in
/-- Extending an automorphism of `hXY.restrict` to `P` along `hX` and `hY` lands in
`P.latticeAut X₀ Y₀`. -/
theorem autCongr_autBaseChangeHom_mem_latticeAut (u : hXY.restrict.Aut) :
    (hXY.baseChangeEquiv hX hY).autCongr (hXY.restrict.autBaseChangeHom S u) ∈
      P.latticeAut X₀ Y₀ := by
  rw [mem_latticeAut_iff, show (X₀ : Set M) = range X₀.subtype by ext; simp,
    show (Y₀ : Set N) = range Y₀.subtype by ext; simp, ← range_comp, ← range_comp]
  exact ⟨(congrArg range
      (funext (hXY.autCongr_autBaseChangeHom_weightEquiv_coe hX hY u))).trans <|
        u.weightEquiv.surjective.range_comp _,
    (congrArg range
      (funext (hXY.autCongr_autBaseChangeHom_coweightEquiv_symm_coe hX hY u))).trans <|
        u.coweightEquiv.symm.surjective.range_comp _⟩

include hX hY in
/-- **Scalar extension of integral automorphisms** into `P.latticeAut X₀ Y₀`. -/
noncomputable def extendAutHom : hXY.restrict.Aut →* P.latticeAut X₀ Y₀ :=
  ((hXY.baseChangeEquiv hX hY).autCongr.toMonoidHom.comp
    (hXY.restrict.autBaseChangeHom S)).codRestrict (P.latticeAut X₀ Y₀)
    (hXY.autCongr_autBaseChangeHom_mem_latticeAut hX hY)

/-- Extending an automorphism of `hXY.restrict` agrees with it on `X₀`. -/
theorem extendAutHom_weightEquiv_coe (u : hXY.restrict.Aut) (x : X₀) :
    ((hXY.extendAutHom hX hY u : P.Aut).weightEquiv (x : M)) = (u.weightEquiv x : M) :=
  hXY.autCongr_autBaseChangeHom_weightEquiv_coe hX hY u x

/-- Extending an automorphism of `hXY.restrict` acts on `(x : M)` by coercing `u • x`. -/
@[simp]
theorem extendAutHom_smul_coe (u : hXY.restrict.Aut) (x : X₀) :
    (hXY.extendAutHom hX hY u : P.Aut) • (x : M) = ((u • x : X₀) : M) :=
  hXY.extendAutHom_weightEquiv_coe hX hY u x

/-- Extending an automorphism of `hXY.restrict` agrees with its forward coweight map on `Y₀`. -/
@[simp]
theorem extendAutHom_coweightEquiv_symm_coe (u : hXY.restrict.Aut) (y : Y₀) :
    ((hXY.extendAutHom hX hY u : P.Aut).coweightEquiv.symm (y : N)) =
      (u.coweightEquiv.symm y : N) :=
  hXY.autCongr_autBaseChangeHom_coweightEquiv_symm_coe hX hY u y

/-- Extending an automorphism preserves its root-index permutation. -/
@[simp]
theorem extendAutHom_indexEquiv (u : hXY.restrict.Aut) :
    (hXY.extendAutHom hX hY u : P.Aut).indexEquiv = u.indexEquiv := by
  ext i; simp [extendAutHom]

/-- Restricting the scalar extension of an integral automorphism recovers that automorphism. -/
@[simp]
theorem restrictAutHom_extendAutHom (u : hXY.restrict.Aut) :
    hXY.restrictAutHom (hXY.extendAutHom hX hY u) = u :=
  Equiv.weightHom_injective _ <| LinearEquiv.ext fun x ↦
    Subtype.ext (hXY.extendAutHom_weightEquiv_coe hX hY u x)

/-- Extending the restriction of a lattice-preserving automorphism recovers that automorphism. -/
@[simp]
theorem extendAutHom_restrictAutHom (g : P.latticeAut X₀ Y₀) :
    hXY.extendAutHom hX hY (hXY.restrictAutHom g) = g := by
  refine Subtype.ext <| Equiv.weightHom_injective P <| LinearEquiv.toLinearMap_injective ?_
  suffices ((hXY.extendAutHom hX hY (hXY.restrictAutHom g) : P.Aut).weightEquiv.toLinearMap) ∘ₗ
      hX.equiv.toLinearMap = (g : P.Aut).weightEquiv.toLinearMap ∘ₗ hX.equiv.toLinearMap from
    LinearMap.ext fun m ↦ by simpa using congr($this (hX.equiv.symm m))
  refine AlgebraTensorModule.ext fun s x ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hX.equiv_tmul, map_smul]
  exact congrArg (s • ·) (hXY.extendAutHom_weightEquiv_coe hX hY (hXY.restrictAutHom g) x)

include hX hY in
/-- **Scalar extension and lattice restriction give an isomorphism
`hXY.restrict.Aut ≃* P.latticeAut X₀ Y₀`.** -/
noncomputable def autMulEquiv : hXY.restrict.Aut ≃* P.latticeAut X₀ Y₀ where
  toFun := hXY.extendAutHom hX hY
  invFun := hXY.restrictAutHom
  left_inv := hXY.restrictAutHom_extendAutHom hX hY
  right_inv := hXY.extendAutHom_restrictAutHom hX hY
  map_mul' := map_mul (hXY.extendAutHom hX hY)

/-- Applying `hXY.autMulEquiv hX hY` is `hXY.extendAutHom hX hY`. -/
@[simp]
theorem autMulEquiv_apply (u : hXY.restrict.Aut) :
    hXY.autMulEquiv hX hY u = hXY.extendAutHom hX hY u :=
  (rfl)

/-- Applying `(hXY.autMulEquiv hX hY).symm` is `hXY.restrictAutHom`. -/
@[simp]
theorem autMulEquiv_symm_apply (g : P.latticeAut X₀ Y₀) :
    (hXY.autMulEquiv hX hY).symm g = hXY.restrictAutHom g :=
  (rfl)

end IsDualLatticePair

end IsBaseChange

section FractionField

variable {ι R K M N : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M]
  [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower R K N]
  {P : RootPairing ι K M N} {X₀ : Submodule R M} {Y₀ : Submodule R N}
  [Module.Free R X₀] [X₀.IsLattice K] [Module.Free R Y₀] [Y₀.IsLattice K]

/-- **For free full lattices over an integral domain in its fraction field, the integral
automorphisms are isomorphic to the lattice-preserving automorphisms of the ambient pairing.** -/
noncomputable def IsDualLatticePair.autMulEquivOfIsLattice (hXY : P.IsDualLatticePair X₀ Y₀) :
    hXY.restrict.Aut ≃* P.latticeAut X₀ Y₀ := by
  have : Module.Finite R Y₀ := Module.Finite.iff_fg.mpr Submodule.IsLattice.fg
  exact hXY.autMulEquiv (Submodule.isBaseChange_subtype X₀) (Submodule.isBaseChange_subtype Y₀)

/-- On `(X₀, Y₀)`, `(autMulEquivOfIsLattice hXY).symm` is lattice restriction `restrictAutHom`. -/
@[simp]
theorem IsDualLatticePair.autMulEquivOfIsLattice_symm_apply (hXY : P.IsDualLatticePair X₀ Y₀)
    (g : P.latticeAut X₀ Y₀) : hXY.autMulEquivOfIsLattice.symm g = hXY.restrictAutHom g :=
  (rfl)

end FractionField

section UnitTmul

variable {ι R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  (D : RootPairing ι R X Y) (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [Free R Y] [Module.Finite R Y]

/-- **The unit-tensor submodules `1 ⊗ X` and `1 ⊗ Y` form a dual `R`-lattice pair inside
`D.baseChange S`** for every root pairing `D` with finite free coweight module. -/
theorem isDualLatticePair_range_mk_one :
    (D.baseChange S).IsDualLatticePair
      (LinearMap.range (TensorProduct.mk R S X 1))
      (LinearMap.range (TensorProduct.mk R S Y 1)) := by
  have hmem : ∀ x ∈ LinearMap.range (TensorProduct.mk R S X 1),
      ∀ y ∈ LinearMap.range (TensorProduct.mk R S Y 1),
        (D.baseChange S).toLinearMap x y ∈ (algebraMap R S).range := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨D.toLinearMap x y, by simp⟩
  refine
    { range_root_subset := by rintro _ ⟨i, rfl⟩; exact ⟨D.root i, by simp⟩
      range_coroot_subset := by rintro _ ⟨i, rfl⟩; exact ⟨D.coroot i, by simp⟩
      pairing_mem_range := hmem
      isPerfPair := ?_ }
  have : Free R X := .of_equiv D.toLinearMap.toPerfPair.symm
  refine LinearMap.IsPerfPair.congr (p := D.toLinearMap)
    (TensorProduct.unitTmulEquiv R S X).symm (TensorProduct.unitTmulEquiv R S Y).symm _ ?_
  ext x y; apply FaithfulSMul.algebraMap_injective R S
  simpa [Algebra.linearMap_apply] using LinearMap.restrictScalarsRange₂_apply
    (LinearMap.range (TensorProduct.mk R S X 1)).subtype
    (LinearMap.range (TensorProduct.mk R S Y 1)).subtype
    (Algebra.linearMap R S) (FaithfulSMul.algebraMap_injective R S)
    (D.baseChange S).toLinearMap (fun m n ↦ hmem m m.2 n n.2)
    (TensorProduct.unitTmulEquiv R S X x) (TensorProduct.unitTmulEquiv R S Y y)

/-- **A root pairing `D` with finite free coweight module is canonically equivalent to the
restriction of `D.baseChange S` to the unit-tensor lattices `1 ⊗ X` and `1 ⊗ Y`.** -/
noncomputable def unitTmulRootPairingEquiv :
    D.Equiv (D.isDualLatticePair_range_mk_one S).restrict := by
  have : Free R X := .of_equiv D.toLinearMap.toPerfPair.symm
  refine
    { weightMap := (TensorProduct.unitTmulEquiv R S X).toLinearMap
      coweightMap := (TensorProduct.unitTmulEquiv R S Y).symm.toLinearMap
      indexEquiv := _root_.Equiv.refl ι
      weight_coweight_transpose := ?_
      root_weightMap := ?_
      coroot_coweightMap := ?_
      bijective_weightMap := (TensorProduct.unitTmulEquiv R S X).bijective
      bijective_coweightMap := (TensorProduct.unitTmulEquiv R S Y).symm.bijective }
  · ext y x; apply FaithfulSMul.algebraMap_injective R S
    obtain ⟨y₀, hy₀⟩ := y.2
    have hy : y = TensorProduct.unitTmulEquiv R S Y y₀ := Subtype.ext (by simpa using hy₀.symm)
    simp [hy]
  · ext i; simp
  · ext i
    exact (TensorProduct.unitTmulEquiv R S Y).injective <| Subtype.ext (by simp)

/-- The weight equivalence of `D.unitTmulRootPairingEquiv S` is `TensorProduct.unitTmulEquiv`. -/
@[simp]
theorem unitTmulRootPairingEquiv_weightEquiv :
    haveI : Free R X := .of_equiv D.toLinearMap.toPerfPair.symm
    (D.unitTmulRootPairingEquiv S).weightEquiv = TensorProduct.unitTmulEquiv R S X :=
  LinearEquiv.toLinearMap_injective rfl

/-- The forward coweight equivalence of `D.unitTmulRootPairingEquiv S` is
`TensorProduct.unitTmulEquiv`. -/
@[simp]
theorem unitTmulRootPairingEquiv_coweightEquiv_symm :
    (D.unitTmulRootPairingEquiv S).coweightEquiv.symm = TensorProduct.unitTmulEquiv R S Y := by
  have h : (D.unitTmulRootPairingEquiv S).coweightEquiv =
      (TensorProduct.unitTmulEquiv R S Y).symm :=
    LinearEquiv.toLinearMap_injective rfl
  rw [h, LinearEquiv.symm_symm]

/-- `D.unitTmulRootPairingEquiv S` acts as the identity on root indices. -/
@[simp]
theorem unitTmulRootPairingEquiv_indexEquiv :
    (D.unitTmulRootPairingEquiv S).indexEquiv = _root_.Equiv.refl ι :=
  (rfl)

/-- Every scalar-extended automorphism `D.autBaseChangeHom S g` preserves the unit-tensor lattices
`1 ⊗ X` and `1 ⊗ Y`. -/
theorem autBaseChangeHom_mem_latticeAut (g : D.Aut) :
    D.autBaseChangeHom S g ∈
      (D.baseChange S).latticeAut
        (LinearMap.range (TensorProduct.mk R S X 1))
        (LinearMap.range (TensorProduct.mk R S Y 1)) := by
  rw [mem_latticeAut_iff, autBaseChangeHom_apply, Equiv.baseChange_weightEquiv,
    Equiv.baseChange_coweightEquiv_symm, LinearMap.coe_range, LinearMap.coe_range,
    ← range_comp, ← range_comp]
  exact ⟨(congrArg range (funext fun x ↦ by simp)).trans (g.weightEquiv.surjective.range_comp _),
    (congrArg range (funext fun y ↦ by simp)).trans
      (g.coweightEquiv.symm.surjective.range_comp _)⟩

/-- Extending the pullback of a restricted unit-tensor automorphism recovers the ambient
automorphism. -/
@[simp]
theorem autBaseChangeHom_symm_autCongr_restrictAutHom
    (g : (D.baseChange S).latticeAut
      (LinearMap.range (TensorProduct.mk R S X 1))
      (LinearMap.range (TensorProduct.mk R S Y 1))) :
    D.autBaseChangeHom S
      ((D.unitTmulRootPairingEquiv S).autCongr.symm
        ((D.isDualLatticePair_range_mk_one S).restrictAutHom g)) = g := by
  let u : D.Aut :=
    (D.unitTmulRootPairingEquiv S).autCongr.symm
      ((D.isDualLatticePair_range_mk_one S).restrictAutHom g)
  refine Equiv.weightHom_injective (D.baseChange S) <|
    LinearEquiv.toLinearMap_injective <| AlgebraTensorModule.ext fun s x ↦ ?_
  have hsmul := (D.unitTmulRootPairingEquiv S).autCongr_smul u x
  rw [MulEquiv.apply_symm_apply] at hsmul
  have : Free R X := .of_equiv D.toLinearMap.toPerfPair.symm
  have hu : (1 : S) ⊗ₜ[R] (u • x) = (g : (D.baseChange S).Aut) • ((1 : S) ⊗ₜ[R] x) := by
    simpa [unitTmulRootPairingEquiv_weightEquiv] using congrArg Subtype.val hsmul.symm
  rw [show s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) by simp [smul_tmul'], map_smul, map_smul]
  -- `weightHom` evaluates `weightEquiv`, which is definitionally the `Aut` SMul action.
  exact congrArg (s • ·) <| (D.autBaseChangeHom_smul_tmul S u 1 x).trans hu

/-- **The exact range of `D.autBaseChangeHom S` is the subgroup of automorphisms of
`D.baseChange S` preserving the unit-tensor lattices `1 ⊗ X` and `1 ⊗ Y`.** -/
theorem range_autBaseChangeHom :
    (D.autBaseChangeHom S).range =
      (D.baseChange S).latticeAut
        (LinearMap.range (TensorProduct.mk R S X 1))
        (LinearMap.range (TensorProduct.mk R S Y 1)) :=
  le_antisymm (by rintro _ ⟨g, rfl⟩; exact D.autBaseChangeHom_mem_latticeAut S g) fun g hg ↦
    ⟨_, D.autBaseChangeHom_symm_autCongr_restrictAutHom S ⟨g, hg⟩⟩

/-- **Scalar extension identifies `D.Aut` with the unit-tensor lattice stabilizer in
`(D.baseChange S).Aut`.** -/
noncomputable def autMulEquivLatticeAutBaseChange :
    D.Aut ≃*
      (D.baseChange S).latticeAut
        (LinearMap.range (TensorProduct.mk R S X 1))
        (LinearMap.range (TensorProduct.mk R S Y 1)) :=
  (MonoidHom.ofInjective (D.autBaseChangeHom_injective S)).trans
    (MulEquiv.subgroupCongr (D.range_autBaseChangeHom S))

/-- Coercing `D.autMulEquivLatticeAutBaseChange S g` to `(D.baseChange S).Aut` is
`D.autBaseChangeHom S g`. -/
@[simp]
theorem coe_autMulEquivLatticeAutBaseChange_apply (g : D.Aut) :
    (D.autMulEquivLatticeAutBaseChange S g : (D.baseChange S).Aut) = D.autBaseChangeHom S g :=
  (rfl)

/-- Restriction to the unit-tensor lattices and pullback along `unitTmulRootPairingEquiv` is the
inverse of `autMulEquivLatticeAutBaseChange`. -/
theorem autMulEquivLatticeAutBaseChange_symm_apply
    (g : (D.baseChange S).latticeAut
      (LinearMap.range (TensorProduct.mk R S X 1))
      (LinearMap.range (TensorProduct.mk R S Y 1))) :
    (D.autMulEquivLatticeAutBaseChange S).symm g =
      (D.unitTmulRootPairingEquiv S).autCongr.symm
        ((D.isDualLatticePair_range_mk_one S).restrictAutHom g) := by
  apply D.autBaseChangeHom_injective S
  rw [← D.coe_autMulEquivLatticeAutBaseChange_apply S, MulEquiv.apply_symm_apply,
    D.autBaseChangeHom_symm_autCongr_restrictAutHom S g]

end UnitTmul

end RootPairing
