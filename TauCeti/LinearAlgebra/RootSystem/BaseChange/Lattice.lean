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

Let `P` be a root pairing over a faithful `R`-algebra `S` on weight and coweight modules `M` and
`N`. An `R`-submodule pair `(X₀, Y₀)` in `M × N` determines the subgroup
`P.latticeAut X₀ Y₀ : Subgroup P.Aut` of automorphisms stabilizing `X₀` under the forward weight
action `g.weightEquiv` and stabilizing `Y₀` under the forward coweight action
`g.coweightEquiv.symm`.

When `X₀` contains all roots, `Y₀` contains all coroots, and `P.toLinearMap` restricts on
`X₀ × Y₀` to a perfect `R`-valued pairing (`P.IsDualLatticePair X₀ Y₀`), the pairing `P` restricts
to an `R`-root pairing `hXY.restrict : RootPairing ι R X₀ Y₀`. Every root reflection stabilizes
both lattices, so `P.weylGroup ≤ P.latticeAut X₀ Y₀`, and every `g ∈ P.latticeAut X₀ Y₀` restricts
to an automorphism of `hXY.restrict` (`hXY.restrictAutHom`).

When `X₀` and `Y₀` are finite free `R`-lattices whose inclusions exhibit `M` and `N` as scalar
extensions along `R → S` (`IsBaseChange S X₀.subtype` and `IsBaseChange S Y₀.subtype` — in
particular for free full lattices over an integral domain inside its fraction field, or for the
unit-tensor lattices `1 ⊗ X` and `1 ⊗ Y` inside `D.baseChange S` of a finite free root datum `D`),
scalar extension and lattice restriction of automorphisms are mutually inverse, giving a canonical
group isomorphism `hXY.autMulEquiv hX hY : hXY.restrict.Aut ≃* P.latticeAut X₀ Y₀`.

## Main definitions

* `RootPairing.latticeAut`: the subgroup of `P.Aut` preserving `X₀` under `weightEquiv` and `Y₀`
  under `coweightEquiv.symm`.
* `RootPairing.IsDualLatticePair`: predicate that `(X₀, Y₀)` contains all roots and coroots and
  carries a restricted perfect `R`-pairing.
* `RootPairing.IsDualLatticePair.restrict`: the restricted `R`-root pairing on `(X₀, Y₀)`.
* `RootPairing.IsDualLatticePair.restrictAutHom`: restriction of automorphisms
  `P.latticeAut X₀ Y₀ →* hXY.restrict.Aut`.
* `RootPairing.IsDualLatticePair.baseChangeEquiv`: the equivalence
  `(hXY.restrict.baseChange S).Equiv P` induced by `IsBaseChange` on `X₀` and `Y₀`.
* `RootPairing.IsDualLatticePair.extendAutHom` and `RootPairing.IsDualLatticePair.autMulEquiv`:
  scalar extension of integral automorphisms and the group isomorphism
  `hXY.restrict.Aut ≃* P.latticeAut X₀ Y₀`.
* `RootPairing.unitTmulRootPairingEquiv` and `RootPairing.autMulEquivLatticeAutBaseChange`:
  comparison of a finite free `R`-root pairing `D` with the unit-tensor lattices in
  `D.baseChange S`.

## Main results

* `RootPairing.mem_latticeAut_iff` and `RootPairing.mem_latticeAut_iff_forall`: setwise and
  elementwise characterizations of `P.latticeAut X₀ Y₀`.
* `RootPairing.IsDualLatticePair.weylGroup_le_latticeAut`: the Weyl group stabilizes every dual
  lattice pair.
* `RootPairing.IsDualLatticePair.restrictAutHom_extendAutHom` and
  `RootPairing.IsDualLatticePair.extendAutHom_restrictAutHom`: scalar extension and restriction of
  automorphisms are mutually inverse.
* `RootPairing.isDualLatticePair_range_mk_one` and `RootPairing.range_autBaseChangeHom`: the
  unit-tensor submodules in `D.baseChange S` form a dual lattice pair whose lattice stabilizer is
  the exact range of `D.autBaseChangeHom S`.

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
    (hg : g ∈ P.latticeAut X₀ Y₀) (x : M) :
    g.weightEquiv.symm x ∈ X₀ ↔ x ∈ X₀ := by
  simpa using (weightEquiv_mem_iff_of_mem_latticeAut hg (g.weightEquiv.symm x)).symm

/-- A lattice-preserving automorphism preserves `Y₀` under `coweightEquiv.symm`. -/
theorem coweightEquiv_symm_mem_iff_of_mem_latticeAut {g : P.Aut}
    (hg : g ∈ P.latticeAut X₀ Y₀) (y : N) :
    g.coweightEquiv.symm y ∈ Y₀ ↔ y ∈ Y₀ :=
  (mem_latticeAut_iff_forall.mp hg).2 y

/-- A lattice-preserving automorphism also preserves `Y₀` under the contravariant map
`coweightEquiv`, since `coweightEquiv` is the inverse of `coweightEquiv.symm`. -/
theorem coweightEquiv_mem_iff_of_mem_latticeAut {g : P.Aut}
    (hg : g ∈ P.latticeAut X₀ Y₀) (y : N) :
    g.coweightEquiv y ∈ Y₀ ↔ y ∈ Y₀ := by
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
theorem root_mem (i : ι) : P.root i ∈ X₀ :=
  hXY.range_root_subset (mem_range_self i)

include hXY in
/-- Every coroot of `P` belongs to `Y₀`. -/
theorem coroot_mem (i : ι) : P.coroot i ∈ Y₀ :=
  hXY.range_coroot_subset (mem_range_self i)

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
    refine LinearMap.IsPerfPair.congr (p := p₀.flip)
      (LinearEquiv.refl R Y₀) (LinearEquiv.refl R X₀) _ ?_
    ext y x
    apply FaithfulSMul.algebraMap_injective R S
    exact (LinearMap.restrictScalarsRange₂_apply Y₀.subtype X₀.subtype
      (Algebra.linearMap R S) (FaithfulSMul.algebraMap_injective R S) P.flip.toLinearMap
      (fun y x ↦ hXY.pairing_mem_range x x.2 y y.2) y x).trans
      (LinearMap.restrictScalarsRange₂_apply X₀.subtype Y₀.subtype
        (Algebra.linearMap R S) (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
        (fun x y ↦ hXY.pairing_mem_range x x.2 y y.2) x y).symm

/-- **Restriction of a root pairing to dual `R`-sublattices `(X₀, Y₀)`.** -/
noncomputable def restrict : RootPairing ι R X₀ Y₀ :=
  let B := LinearMap.restrictScalarsRange₂ X₀.subtype Y₀.subtype (Algebra.linearMap R S)
    (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
    fun x y ↦ hXY.pairing_mem_range x x.2 y y.2
  { toLinearMap := B
    isPerfPair_toLinearMap := hXY.isPerfPair
    root := ⟨fun i ↦ ⟨P.root i, hXY.root_mem i⟩,
      fun _ _ h ↦ P.root.injective (congrArg Subtype.val h)⟩
    coroot := ⟨fun i ↦ ⟨P.coroot i, hXY.coroot_mem i⟩,
      fun _ _ h ↦ P.coroot.injective (congrArg Subtype.val h)⟩
    root_coroot_two i := FaithfulSMul.algebraMap_injective R S <|
      (LinearMap.restrictScalarsRange₂_apply X₀.subtype Y₀.subtype
        (Algebra.linearMap R S) (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
        (fun x y ↦ hXY.pairing_mem_range x x.2 y y.2)
        ⟨P.root i, hXY.root_mem i⟩ ⟨P.coroot i, hXY.coroot_mem i⟩).trans <|
        (P.root_coroot_two i).trans (map_ofNat (algebraMap R S) 2).symm
    reflectionPerm := P.reflectionPerm
    reflectionPerm_root i j := Subtype.ext <| by
      have h : algebraMap R S (B ⟨P.root j, hXY.root_mem j⟩ ⟨P.coroot i, hXY.coroot_mem i⟩) =
          P.toLinearMap (P.root j) (P.coroot i) :=
        LinearMap.restrictScalarsRange₂_apply X₀.subtype Y₀.subtype
          (Algebra.linearMap R S) (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
          (fun x y ↦ hXY.pairing_mem_range x x.2 y y.2)
          ⟨P.root j, hXY.root_mem j⟩ ⟨P.coroot i, hXY.coroot_mem i⟩
      exact calc
        P.root j - B ⟨P.root j, hXY.root_mem j⟩ ⟨P.coroot i, hXY.coroot_mem i⟩ • P.root i
            = P.root j - algebraMap R S
                (B ⟨P.root j, hXY.root_mem j⟩ ⟨P.coroot i, hXY.coroot_mem i⟩) • P.root i := by
              rw [algebraMap_smul]
          _ = P.root j - P.toLinearMap (P.root j) (P.coroot i) • P.root i := by rw [h]
          _ = P.root (P.reflectionPerm i j) := P.reflectionPerm_root i j
    reflectionPerm_coroot i j := Subtype.ext <| by
      have h : algebraMap R S (B ⟨P.root i, hXY.root_mem i⟩ ⟨P.coroot j, hXY.coroot_mem j⟩) =
          P.toLinearMap (P.root i) (P.coroot j) :=
        LinearMap.restrictScalarsRange₂_apply X₀.subtype Y₀.subtype
          (Algebra.linearMap R S) (FaithfulSMul.algebraMap_injective R S) P.toLinearMap
          (fun x y ↦ hXY.pairing_mem_range x x.2 y y.2)
          ⟨P.root i, hXY.root_mem i⟩ ⟨P.coroot j, hXY.coroot_mem j⟩
      exact calc
        P.coroot j - B ⟨P.root i, hXY.root_mem i⟩ ⟨P.coroot j, hXY.coroot_mem j⟩ • P.coroot i
            = P.coroot j - algebraMap R S
                (B ⟨P.root i, hXY.root_mem i⟩ ⟨P.coroot j, hXY.coroot_mem j⟩) • P.coroot i := by
              rw [algebraMap_smul]
          _ = P.coroot j - P.toLinearMap (P.root i) (P.coroot j) • P.coroot i := by rw [h]
          _ = P.coroot (P.reflectionPerm i j) := P.reflectionPerm_coroot i j }

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
    [IsScalarTower T R S] [P.IsValuedIn T] :
    hXY.restrict.IsValuedIn T where
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
theorem isCrystallographic_restrict [P.IsCrystallographic] :
    hXY.restrict.IsCrystallographic :=
  hXY.isValuedIn_restrict ℤ

/-- Restriction of a reduced root pairing along a faithful algebra is reduced. -/
theorem isReduced_restrict [P.IsReduced] : hXY.restrict.IsReduced where
  eq_or_eq_neg i j h := by
    have hS : ¬ LinearIndependent S ![P.root i, P.root j] := by
      refine fun hli ↦ h ?_
      have hliR : LinearIndependent R ![P.root i, P.root j] :=
        hli.restrict_scalars <| by
          simp_rw [← Algebra.algebraMap_eq_smul_one]
          exact FaithfulSMul.algebraMap_injective R S
      have hcomp :
          ![P.root i, P.root j] = X₀.subtype ∘ ![hXY.restrict.root i, hXY.restrict.root j] := by
        ext k; fin_cases k <;> rfl
      rw [hcomp] at hliR
      exact hliR.of_comp
    rcases IsReduced.eq_or_eq_neg (P := P) i j hS with hij | hij
    · exact .inl (Subtype.ext hij)
    · exact .inr (Subtype.ext hij)

include hXY in
/-- Every root reflection of `P` stabilizes both lattices of a dual lattice pair. -/
theorem reflection_mem_latticeAut (i : ι) :
    Equiv.reflection P i ∈ P.latticeAut X₀ Y₀ := by
  have hmemX (x : M) (hx : x ∈ X₀) : P.reflection i x ∈ X₀ := by
    rw [← hXY.restrict_coe_reflection i ⟨x, hx⟩]
    exact (hXY.restrict.reflection i ⟨x, hx⟩).2
  have hmemY (y : N) (hy : y ∈ Y₀) : P.coreflection i y ∈ Y₀ := by
    rw [← hXY.restrict_coe_coreflection i ⟨y, hy⟩]
    exact (hXY.restrict.coreflection i ⟨y, hy⟩).2
  refine mem_latticeAut_iff_forall.mpr ⟨fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [Equiv.reflection_weightEquiv]
    exact ⟨fun hx ↦ P.reflection_same i x ▸ hmemX _ hx, hmemX x⟩
  · have hsymm : (Equiv.reflection P i).coweightEquiv.symm y = P.coreflection i y := by
      simpa using congr($(Equiv.forwardCoweightHom_reflection P i) y)
    rw [hsymm]
    exact ⟨fun hy ↦ P.coreflection_same i y ▸ hmemY _ hy, hmemY y⟩

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
      ext y x
      apply FaithfulSMul.algebraMap_injective R S
      simpa [eX, eY] using (g : P.Aut).toLinearMap_weightEquiv (x : M) (y : N)
    root_weightMap := by
      ext i
      simp only [LinearEquiv.coe_coe, comp_apply, restrict_coe_root, Equiv.root_indexEquiv_eq_smul]
      rfl
    coroot_coweightMap := by
      ext i
      simpa [eY] using (g : P.Aut).coroot_coweightMap_apply P P i
    bijective_weightMap := eX.bijective
    bijective_coweightMap := eY.bijective }

/-- **Restriction of lattice-preserving automorphisms**, as a group homomorphism
`P.latticeAut X₀ Y₀ →* hXY.restrict.Aut`. -/
noncomputable def restrictAutHom : P.latticeAut X₀ Y₀ →* hXY.restrict.Aut where
  toFun := hXY.restrictAut
  map_one' := by
    apply Equiv.weightHom_injective
    ext x
    rfl
  map_mul' g₁ g₂ := by
    apply Equiv.weightHom_injective
    ext x
    rfl

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
  rw [LinearEquiv.apply_symm_apply]
  have h : ((hXY.restrictAutHom g).coweightEquiv
      ((hXY.restrictAutHom g).coweightEquiv.symm y) : N) =
      (g : P.Aut).coweightEquiv ((hXY.restrictAutHom g).coweightEquiv.symm y : N) := rfl
  rw [← h, LinearEquiv.apply_symm_apply]

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
      Equiv.reflection hXY.restrict i := by
  apply Equiv.weightHom_injective
  ext x
  exact hXY.restrict_coe_reflection i x |>.symm

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
      refine TensorProduct.AlgebraTensorModule.ext fun b y ↦ ?_
      refine TensorProduct.AlgebraTensorModule.ext fun a x ↦ ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      simp [hX.equiv_tmul, hY.equiv_tmul]
      ring
    refine LinearMap.ext fun n ↦ ?_
    simpa using congr($hcomp (hY.equiv.symm n))
  root_weightMap := by
    ext i
    simp [hX.equiv_tmul]
  coroot_coweightMap := by
    ext i
    simpa using hY.equiv_symm_apply (hXY.restrict.coroot i)
  bijective_weightMap := hX.equiv.bijective
  bijective_coweightMap := hY.equiv.symm.bijective

/-- The weight equivalence of `hXY.baseChangeEquiv hX hY` is `hX.equiv`. -/
@[simp]
theorem baseChangeEquiv_weightEquiv :
    (hXY.baseChangeEquiv hX hY).weightEquiv = hX.equiv :=
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

include hX hY in
/-- Extending an automorphism of `hXY.restrict` to `P` along `hX` and `hY` lands in
`P.latticeAut X₀ Y₀`. -/
theorem autCongr_autBaseChangeHom_mem_latticeAut (u : hXY.restrict.Aut) :
    (hXY.baseChangeEquiv hX hY).autCongr (hXY.restrict.autBaseChangeHom S u) ∈
      P.latticeAut X₀ Y₀ := by
  let e := hXY.baseChangeEquiv hX hY
  let φ : hXY.restrict.Aut →* P.Aut :=
    e.autCongr.toMonoidHom.comp (hXY.restrict.autBaseChangeHom S)
  have hX_apply (v : hXY.restrict.Aut) (x : X₀) :
      (φ v).weightEquiv (x : M) = (v.weightEquiv x : M) := by
    have h := e.autCongr_smul (hXY.restrict.autBaseChangeHom S v) (1 ⊗ₜ[R] x)
    rw [hXY.restrict.autBaseChangeHom_smul_tmul, baseChangeEquiv_weightEquiv,
      hX.equiv_tmul, hX.equiv_tmul, one_smul, one_smul] at h
    exact h
  have hY_apply (v : hXY.restrict.Aut) (y : Y₀) :
      (φ v).coweightEquiv.symm (y : N) = (v.coweightEquiv.symm y : N) := by
    let gv := hXY.restrict.autBaseChangeHom S v
    have h : (e.autCongr gv).coweightEquiv.symm (e.coweightEquiv.symm (1 ⊗ₜ[R] y)) =
        e.coweightEquiv.symm (gv.coweightEquiv.symm (1 ⊗ₜ[R] y)) :=
      (e.autCongr gv).coweightEquiv.injective <| by
        rw [LinearEquiv.apply_symm_apply, e.coweightEquiv_autCongr_apply,
          LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [hXY.restrict.autBaseChangeHom_coweightEquiv_symm_tmul,
      baseChangeEquiv_coweightEquiv_symm, hY.equiv_tmul, hY.equiv_tmul, one_smul, one_smul] at h
    exact h
  refine mem_latticeAut_iff_forall.mpr ⟨fun x ↦ ?_, fun y ↦ ?_⟩
  · refine ⟨fun hx ↦ ?_, fun hx ↦ hX_apply u ⟨x, hx⟩ ▸ (u.weightEquiv ⟨x, hx⟩).2⟩
    have hinv := (u⁻¹.weightEquiv ⟨(φ u).weightEquiv x, hx⟩).2
    have hcomp : (φ u⁻¹).weightEquiv ((φ u).weightEquiv x) = x := by
      have hmul : φ u⁻¹ * φ u = 1 := by simp
      exact congr($((congrArg (Equiv.weightHom P) hmul)) x)
    rwa [← hX_apply u⁻¹, hcomp] at hinv
  · refine ⟨fun hy ↦ ?_, fun hy ↦ hY_apply u ⟨y, hy⟩ ▸ (u.coweightEquiv.symm ⟨y, hy⟩).2⟩
    have hinv := (u⁻¹.coweightEquiv.symm ⟨(φ u).coweightEquiv.symm y, hy⟩).2
    have hcomp : (φ u⁻¹).coweightEquiv.symm ((φ u).coweightEquiv.symm y) = y := by
      rw [← Equiv.forwardCoweightHom_apply, ← Equiv.forwardCoweightHom_apply,
        ← mul_apply_eq_comp, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
      rfl
    rwa [← hY_apply u⁻¹, hcomp] at hinv

include hX hY in
/-- **Scalar extension of integral automorphisms** into `P.latticeAut X₀ Y₀`. -/
noncomputable def extendAutHom : hXY.restrict.Aut →* P.latticeAut X₀ Y₀ :=
  ((hXY.baseChangeEquiv hX hY).autCongr.toMonoidHom.comp
    (hXY.restrict.autBaseChangeHom S)).codRestrict (P.latticeAut X₀ Y₀)
    (hXY.autCongr_autBaseChangeHom_mem_latticeAut hX hY)

/-- Extending an automorphism of `hXY.restrict` agrees with it on `X₀`. -/
theorem extendAutHom_weightEquiv_coe (u : hXY.restrict.Aut) (x : X₀) :
    ((hXY.extendAutHom hX hY u : P.Aut).weightEquiv (x : M)) = (u.weightEquiv x : M) := by
  have h := (hXY.baseChangeEquiv hX hY).autCongr_smul
    (hXY.restrict.autBaseChangeHom S u) (1 ⊗ₜ[R] x)
  rw [hXY.restrict.autBaseChangeHom_smul_tmul, baseChangeEquiv_weightEquiv,
    hX.equiv_tmul, hX.equiv_tmul, one_smul, one_smul] at h
  exact h

/-- Extending an automorphism of `hXY.restrict` acts on `(x : M)` by coercing `u • x`. -/
@[simp]
theorem extendAutHom_smul_coe (u : hXY.restrict.Aut) (x : X₀) :
    (hXY.extendAutHom hX hY u : P.Aut) • (x : M) = ((u • x : X₀) : M) :=
  hXY.extendAutHom_weightEquiv_coe hX hY u x

/-- Extending an automorphism of `hXY.restrict` agrees with its forward coweight map on `Y₀`. -/
@[simp]
theorem extendAutHom_coweightEquiv_symm_coe (u : hXY.restrict.Aut) (y : Y₀) :
    ((hXY.extendAutHom hX hY u : P.Aut).coweightEquiv.symm (y : N)) =
      (u.coweightEquiv.symm y : N) := by
  let e := hXY.baseChangeEquiv hX hY
  let g := hXY.restrict.autBaseChangeHom S u
  have h : (e.autCongr g).coweightEquiv.symm (e.coweightEquiv.symm (1 ⊗ₜ[R] y)) =
      e.coweightEquiv.symm (g.coweightEquiv.symm (1 ⊗ₜ[R] y)) :=
    (e.autCongr g).coweightEquiv.injective <| by
      rw [LinearEquiv.apply_symm_apply, e.coweightEquiv_autCongr_apply,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hXY.restrict.autBaseChangeHom_coweightEquiv_symm_tmul,
    baseChangeEquiv_coweightEquiv_symm, hY.equiv_tmul, hY.equiv_tmul, one_smul, one_smul] at h
  exact h

/-- Extending an automorphism preserves its root-index permutation. -/
@[simp]
theorem extendAutHom_indexEquiv (u : hXY.restrict.Aut) :
    (hXY.extendAutHom hX hY u : P.Aut).indexEquiv = u.indexEquiv := by
  ext i
  simp [extendAutHom]

/-- Restricting the scalar extension of an integral automorphism recovers that automorphism. -/
@[simp]
theorem restrictAutHom_extendAutHom (u : hXY.restrict.Aut) :
    hXY.restrictAutHom (hXY.extendAutHom hX hY u) = u := by
  apply Equiv.weightHom_injective
  ext x
  exact hXY.extendAutHom_weightEquiv_coe hX hY u x

/-- Extending the restriction of a lattice-preserving automorphism recovers that automorphism. -/
@[simp]
theorem extendAutHom_restrictAutHom (g : P.latticeAut X₀ Y₀) :
    hXY.extendAutHom hX hY (hXY.restrictAutHom g) = g := by
  apply Subtype.ext
  apply Equiv.weightHom_injective P
  apply LinearEquiv.toLinearMap_injective
  suffices ((hXY.extendAutHom hX hY (hXY.restrictAutHom g) : P.Aut).weightEquiv.toLinearMap) ∘ₗ
      hX.equiv.toLinearMap = (g : P.Aut).weightEquiv.toLinearMap ∘ₗ hX.equiv.toLinearMap by
    ext m
    simpa using congr($this (hX.equiv.symm m))
  refine TensorProduct.AlgebraTensorModule.ext fun s x ↦ ?_
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
    (g : P.latticeAut X₀ Y₀) :
    hXY.autMulEquivOfIsLattice.symm g = hXY.restrictAutHom g :=
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
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨D.toLinearMap x y, by simp⟩
  refine
    { range_root_subset := by rintro _ ⟨i, rfl⟩; exact ⟨D.root i, by simp⟩
      range_coroot_subset := by rintro _ ⟨i, rfl⟩; exact ⟨D.coroot i, by simp⟩
      pairing_mem_range := hmem
      isPerfPair := ?_ }
  have : Free R X := .of_equiv D.toLinearMap.toPerfPair.symm
  refine LinearMap.IsPerfPair.congr (p := D.toLinearMap)
    (TensorProduct.unitTmulEquiv R S X).symm
    (TensorProduct.unitTmulEquiv R S Y).symm _ ?_
  ext x y
  apply FaithfulSMul.algebraMap_injective R S
  have h := LinearMap.restrictScalarsRange₂_apply
    (LinearMap.range (TensorProduct.mk R S X 1)).subtype
    (LinearMap.range (TensorProduct.mk R S Y 1)).subtype
    (Algebra.linearMap R S) (FaithfulSMul.algebraMap_injective R S)
    (D.baseChange S).toLinearMap (fun m n ↦ hmem m m.2 n n.2)
    (TensorProduct.unitTmulEquiv R S X x) (TensorProduct.unitTmulEquiv R S Y y)
  simpa [Algebra.linearMap_apply] using h

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
  · ext y x
    apply FaithfulSMul.algebraMap_injective R S
    obtain ⟨y₀, hy₀⟩ := y.2
    have hy : y = TensorProduct.unitTmulEquiv R S Y y₀ :=
      Subtype.ext (by simpa using hy₀.symm)
    simp [hy]
  · ext i
    simp
  · ext i
    apply (TensorProduct.unitTmulEquiv R S Y).injective
    apply Subtype.ext
    simp

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
  refine mem_latticeAut_iff_forall.mpr ⟨fun z ↦ ?_, fun w ↦ ?_⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      refine ⟨g.weightEquiv.symm x, ?_⟩
      apply (D.autBaseChangeHom S g).weightEquiv.injective
      -- `Aut` SMul on weights is evaluation of `weightEquiv`.
      change D.autBaseChangeHom S g • TensorProduct.mk R S X 1 (g.weightEquiv.symm x) =
        (D.autBaseChangeHom S g).weightEquiv z
      rw [TensorProduct.mk_apply, D.autBaseChangeHom_smul_tmul, ← hx, TensorProduct.mk_apply]
      congr 1
      exact g.weightEquiv.apply_symm_apply x
    · rintro ⟨x, rfl⟩
      refine ⟨g.weightEquiv x, ?_⟩
      -- `Aut` SMul on weights is evaluation of `weightEquiv`.
      change TensorProduct.mk R S X 1 (g.weightEquiv x) =
        D.autBaseChangeHom S g • TensorProduct.mk R S X 1 x
      rw [TensorProduct.mk_apply, TensorProduct.mk_apply, D.autBaseChangeHom_smul_tmul]
      rfl
  · refine ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      refine ⟨g.coweightEquiv y, ?_⟩
      apply (D.autBaseChangeHom S g).coweightEquiv.symm.injective
      rw [TensorProduct.mk_apply, D.autBaseChangeHom_coweightEquiv_symm_tmul,
        LinearEquiv.symm_apply_apply, ← hy, TensorProduct.mk_apply]
    · rintro ⟨y, rfl⟩
      refine ⟨g.coweightEquiv.symm y, ?_⟩
      rw [TensorProduct.mk_apply, TensorProduct.mk_apply,
        D.autBaseChangeHom_coweightEquiv_symm_tmul]

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
  apply Equiv.weightHom_injective (D.baseChange S)
  apply LinearEquiv.toLinearMap_injective
  refine TensorProduct.AlgebraTensorModule.ext fun s x ↦ ?_
  have hsmul := (D.unitTmulRootPairingEquiv S).autCongr_smul u x
  rw [MulEquiv.apply_symm_apply] at hsmul
  have hu : (1 : S) ⊗ₜ[R] (u • x) = (g : (D.baseChange S).Aut) • ((1 : S) ⊗ₜ[R] x) := by
    have : Free R X := .of_equiv D.toLinearMap.toPerfPair.symm
    simpa [unitTmulRootPairingEquiv_weightEquiv] using congrArg Subtype.val hsmul.symm
  have hs : s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) := by simp [smul_tmul']
  rw [hs, map_smul, map_smul]
  refine congrArg (s • ·) ?_
  -- `weightHom` evaluates `weightEquiv`, which is definitionally the `Aut` SMul action.
  change D.autBaseChangeHom S u • ((1 : S) ⊗ₜ[R] x) =
    (g : (D.baseChange S).Aut) • ((1 : S) ⊗ₜ[R] x)
  rw [D.autBaseChangeHom_smul_tmul, hu]

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
    (D.autMulEquivLatticeAutBaseChange S g : (D.baseChange S).Aut) =
      D.autBaseChangeHom S g :=
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
