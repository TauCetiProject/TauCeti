/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Base
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Lattice
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
import TauCeti.LinearAlgebra.RootSystem.Isomorphism
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Based automorphisms and dual isogeny lattices under base change

This file connects `TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut` with scalar extension
(`RootPairing.baseChange`, `RootPairing.Base.baseChange`) and dual-lattice restriction
(`RootPairing.IsDualLatticePair.restrict`): lattice restriction of bases
(`IsDualLatticePair.restrictBase`), compatibility of based automorphisms with scalar extension and
the open-chamber criterion over an ordered field
(`Base.mem_basedAut_iff_smul_openDominantChamber_baseChange`), the restricted semidirect product
`P.weylGroup ⋊ ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) ≃* P.latticeAut X₀ Y₀`
(`Base.latticeAutSemidirectProductMulEquiv`), and the Cartan-matrix lift criterion for spanning
ambient pairings (`Base.exists_basedAut_inf_latticeAut_forall_indexEquiv_eq_iff`).

## Main definitions

* `RootPairing.IsDualLatticePair.restrictBase` and `RootPairing.IsDualLatticePair.basedAutMulEquiv`:
  lattice restriction of bases and
  `(hXY.restrictBase b).basedAut ≃* ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)` when `Y₀` is finite free
  over `R` and `X₀.subtype`, `Y₀.subtype` satisfy `IsBaseChange S`.
* `RootPairing.Base.latticeAutSemidirectProductMulEquiv`: the restricted semidirect product
  `P.weylGroup ⋊ ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) ≃* P.latticeAut X₀ Y₀` whenever
  `P.weylGroup ≤ P.latticeAut X₀ Y₀` (in particular for every dual lattice pair via
  `IsDualLatticePair.weylGroup_le_latticeAut`).

## Main results

* `RootPairing.Base.autBaseChangeHom_mem_basedAut_iff` and
  `RootPairing.Base.mem_basedAut_iff_smul_openDominantChamber_baseChange`: scalar extension
  preserves and reflects based automorphisms and characterizes them via the open dominant chamber.
* `RootPairing.Base.isComplement'_weylGroup_basedAut_subgroupOf` and
  `RootPairing.Base.exists_basedAut_inf_latticeAut_forall_indexEquiv_eq_iff`: Weyl complement inside
  `P.latticeAut X₀ Y₀` and Cartan-matrix lift criterion for submodule pairs.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7,
  and 7.4.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C,
  C.43, C.51, and C.53.
-/

public section

open Module Pointwise Set

namespace RootPairing

/-! ### Based automorphisms under scalar extension -/

section BaseBaseChange

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base) (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [Flat R S] [Free R N] [Module.Finite R N]

/-- Transporting `b.baseChange S` by `P.autBaseChangeHom S g` is `(b.map g).baseChange S`. -/
@[simp] theorem Base.map_autBaseChangeHom (g : P.Aut) :
    (b.baseChange S).map (P.autBaseChangeHom S g) = (b.map g).baseChange S := by
  classical exact Base.ext_iff.mpr (by simp [Base.support_map_eq])

/-- Scalar extension preserves and reflects membership in `basedAut`. -/
theorem Base.autBaseChangeHom_mem_basedAut_iff {g : P.Aut} :
    P.autBaseChangeHom S g ∈ (b.baseChange S).basedAut ↔ g ∈ b.basedAut := by
  simp [Base.mem_basedAut_iff]

end BaseBaseChange

/-- **An automorphism of a finite reduced crystallographic root pairing is based if and only if
its scalar extension to an ordered field `K` (such as `ℚ` or `ℝ`) preserves the open dominant
chamber of `b.baseChange K`** (which by `RootPairing.preimage_rootSpanProj_openDominantChamber`
is the open cylinder chamber over `(P.baseChange K).restrictScalars' K`). -/
theorem Base.mem_basedAut_iff_smul_openDominantChamber_baseChange {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N}
    [Finite ι] [P.IsCrystallographic] [P.IsReduced] [Free R N] [Module.Finite R N] (b : P.Base)
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra R K]
    [FaithfulSMul R K] [Flat R K] {g : P.Aut} :
    g ∈ b.basedAut ↔
      P.autBaseChangeHom K g • openDominantChamber (P.baseChange K) (b.baseChange K) =
        openDominantChamber (P.baseChange K) (b.baseChange K) :=
  let _ := (P.baseChange K).flip_isReduced
  (b.autBaseChangeHom_mem_basedAut_iff K).symm.trans
    (b.baseChange K).mem_basedAut_iff_smul_openDominantChamber

/-! ### Lattice restriction of bases and based automorphisms -/

section LatticeBase

variable {ι R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {P : RootPairing ι S M N} {X₀ : Submodule R M} {Y₀ : Submodule R N}

namespace IsDualLatticePair

variable (hXY : P.IsDualLatticePair X₀ Y₀)

/-- **Restriction of a base `b : P.Base` to a dual `R`-lattice pair `(X₀, Y₀)`.** -/
noncomputable def restrictBase (b : P.Base) : hXY.restrict.Base :=
  b.comapOfInjective X₀.subtype Y₀.subtype Subtype.val_injective Subtype.val_injective
    hXY.restrict_coe_root hXY.restrict_coe_coroot

/-- Lattice restriction of a base leaves `support` unchanged. -/
@[simp] theorem support_restrictBase (b : P.Base) : (hXY.restrictBase b).support = b.support :=
  Base.support_comapOfInjective ..

/-- Lattice restriction of bases commutes with transporting by `hXY.restrictAutHom`. -/
@[simp] theorem map_restrictAutHom (b : P.Base) (g : P.latticeAut X₀ Y₀) :
    (hXY.restrictBase b).map (hXY.restrictAutHom g) = hXY.restrictBase (b.map (g : P.Aut)) := by
  classical exact Base.ext_iff.mpr (by simp [Base.support_map_eq])

/-- A restricted automorphism fixes `hXY.restrictBase b` iff the ambient automorphism fixes `b`. -/
theorem restrictAutHom_mem_basedAut_iff (b : P.Base) {g : P.latticeAut X₀ Y₀} :
    hXY.restrictAutHom g ∈ (hXY.restrictBase b).basedAut ↔ (g : P.Aut) ∈ b.basedAut := by
  simp [Base.mem_basedAut_iff]

/-- Lattice restriction preserves every entry of the `T`-valued Cartan matrix of a base. -/
@[simp] theorem cartanMatrixIn_restrictBase_apply (b : P.Base) (T : Type*) [CommRing T]
    [Algebra T R] [Algebra T S] [IsScalarTower T R S] [FaithfulSMul T S] [P.IsValuedIn T]
    (i j : (hXY.restrictBase b).support) :
    (hXY.restrictBase b).cartanMatrixIn T i j =
      b.cartanMatrixIn T ⟨i, (hXY.support_restrictBase b).le i.property⟩
        ⟨j, (hXY.support_restrictBase b).le j.property⟩ := by simp [Base.cartanMatrixIn_def]

/-- Lattice restriction preserves every entry of the integral Cartan matrix of a crystallographic
root pairing. -/
theorem cartanMatrix_restrictBase_apply [CharZero S] [P.IsCrystallographic] (b : P.Base)
    (i j : (hXY.restrictBase b).support) :
    (hXY.restrictBase b).cartanMatrix i j =
      b.cartanMatrix ⟨i, (hXY.support_restrictBase b).le i.property⟩
        ⟨j, (hXY.support_restrictBase b).le j.property⟩ :=
  hXY.cartanMatrixIn_restrictBase_apply b ℤ i j

section BaseChangeLattices

variable [Free R Y₀] [Module.Finite R Y₀]
  (hX : IsBaseChange S X₀.subtype) (hY : IsBaseChange S Y₀.subtype)

/-- Extending an integral automorphism preserves `b` iff it preserves `hXY.restrictBase b`. -/
theorem extendAutHom_mem_basedAut_iff (b : P.Base) {u : hXY.restrict.Aut} :
    (hXY.extendAutHom hX hY u : P.Aut) ∈ b.basedAut ↔ u ∈ (hXY.restrictBase b).basedAut := by
  simp [Base.mem_basedAut_iff]

include hX hY in
/-- **Scalar extension and lattice restriction identify `(hXY.restrictBase b).basedAut` with the
based lattice-preserving automorphisms `↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)`** when `Y₀` is finite
free over `R` and `X₀.subtype`, `Y₀.subtype` satisfy `IsBaseChange S`. -/
noncomputable def basedAutMulEquiv (b : P.Base) :
    (hXY.restrictBase b).basedAut ≃* ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) where
  toFun u := ⟨(hXY.extendAutHom hX hY u : P.Aut),
    (hXY.extendAutHom_mem_basedAut_iff hX hY b).mpr u.property,
    (hXY.extendAutHom hX hY u).property⟩
  invFun g := ⟨hXY.restrictAutHom ⟨g.val, g.property.right⟩,
    (hXY.restrictAutHom_mem_basedAut_iff b).mpr g.property.left⟩
  left_inv u := Subtype.ext (hXY.restrictAutHom_extendAutHom hX hY u)
  right_inv g := Subtype.ext <| congrArg (fun x : P.latticeAut X₀ Y₀ ↦ (x : P.Aut))
    (hXY.extendAutHom_restrictAutHom hX hY ⟨g.val, g.property.right⟩)
  map_mul' u v := Subtype.ext <| congrArg (fun x : P.latticeAut X₀ Y₀ ↦ (x : P.Aut))
    (map_mul (hXY.extendAutHom hX hY) u.val v.val)

/-- Coercing `hXY.basedAutMulEquiv hX hY b u` to `P.Aut` applies `hXY.extendAutHom hX hY`. -/
@[simp] theorem coe_basedAutMulEquiv_apply (b : P.Base) (u : (hXY.restrictBase b).basedAut) :
    (hXY.basedAutMulEquiv hX hY b u : P.Aut) = hXY.extendAutHom hX hY u := (rfl)

/-- Coercing `(hXY.basedAutMulEquiv hX hY b).symm g` applies `hXY.restrictAutHom`. -/
@[simp] theorem coe_basedAutMulEquiv_symm_apply (b : P.Base)
    (g : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)) :
    ((hXY.basedAutMulEquiv hX hY b).symm g : hXY.restrict.Aut) =
      hXY.restrictAutHom ⟨g.val, g.property.right⟩ := (rfl)

/-- Extending `hXY.restrictBase b` to `S` and transporting along `hXY.baseChangeEquiv hX hY`
recovers `b`. -/
@[simp] theorem map_baseChange_restrictBase [Flat R S] (b : P.Base) :
    ((hXY.restrictBase b).baseChange S).map (hXY.baseChangeEquiv hX hY) = b := by
  classical exact Base.ext_iff.mpr (by simp [Base.support_map_eq])

end BaseChangeLattices

end IsDualLatticePair

/-- Extending a base `b : D.Base` to `D.baseChange S` and restricting to the unit-tensor lattices
`1 ⊗ X` and `1 ⊗ Y` recovers `b` transported along `D.unitTmulRootPairingEquiv S`. -/
@[simp] theorem restrictBase_baseChange {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (D : RootPairing ι R X Y) [Flat R S]
    [Free R Y] [Module.Finite R Y] (b : D.Base) :
    (D.isDualLatticePair_range_mk_one S).restrictBase (b.baseChange S) =
      b.map (D.unitTmulRootPairingEquiv S) := by
  classical exact Base.ext_iff.mpr (by simp [Base.support_map_eq])

end LatticeBase

/-! ### Restricted semidirect product for dual isogeny lattices -/

section LatticeSemidirect

variable {ι R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module S M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
  {P : RootPairing ι S M N}

namespace Base

/-- Conjugation action of `↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)` on `P.weylGroup`, obtained by
restricting `b.conjWeylGroup`. -/
noncomputable def conjWeylGroupLatticeAut (b : P.Base) (X₀ : Submodule R M) (Y₀ : Submodule R N) :
    ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) →* MulAut P.weylGroup :=
  b.conjWeylGroup.comp (Subgroup.inclusion inf_le_left)

/-- A based lattice-preserving automorphism `δ` acts on `P.weylGroup` by `w ↦ δ w δ⁻¹`. -/
@[simp] theorem coe_conjWeylGroupLatticeAut_apply (b : P.Base) (X₀ : Submodule R M)
    (Y₀ : Submodule R N) (δ : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)) (w : P.weylGroup) :
    (b.conjWeylGroupLatticeAut X₀ Y₀ δ w : P.Aut) = (δ : P.Aut) * w * (δ : P.Aut)⁻¹ :=
  b.coe_conjWeylGroup_apply ⟨δ.val, δ.property.left⟩ w

variable [Finite ι] [CharZero S] [IsDomain S] [P.IsCrystallographic] [P.IsReduced]

section WeylLeLatticeAut

variable (b : P.Base) {X₀ : Submodule R M} {Y₀ : Submodule R N}
  (hW : P.weylGroup ≤ P.latticeAut X₀ Y₀)

include hW

/-- The Weyl factor of any automorphism preserves `(X₀, Y₀)` whenever
`P.weylGroup ≤ P.latticeAut X₀ Y₀`. -/
theorem semidirectProductMulEquiv_symm_left_mem_latticeAut (g : P.Aut) :
    ((b.semidirectProductMulEquiv.symm g).left : P.Aut) ∈ P.latticeAut X₀ Y₀ :=
  hW (b.semidirectProductMulEquiv.symm g).left.property

/-- The based factor of a lattice-preserving automorphism preserves `(X₀, Y₀)` whenever
`P.weylGroup ≤ P.latticeAut X₀ Y₀`. -/
theorem semidirectProductMulEquiv_symm_right_mem_latticeAut {g : P.Aut}
    (hg : g ∈ P.latticeAut X₀ Y₀) :
    ((b.semidirectProductMulEquiv.symm g).right : P.Aut) ∈ P.latticeAut X₀ Y₀ :=
  (b.coe_semidirectProductMulEquiv_symm_right g).symm ▸
    mul_mem (inv_mem (b.semidirectProductMulEquiv_symm_left_mem_latticeAut hW g)) hg

/-- **The Weyl group complements the based automorphisms inside `P.latticeAut X₀ Y₀`** whenever
`P.weylGroup ≤ P.latticeAut X₀ Y₀` (in particular for every dual lattice pair via
`IsDualLatticePair.weylGroup_le_latticeAut`). -/
theorem isComplement'_weylGroup_basedAut_subgroupOf :
    (P.weylGroup.subgroupOf (P.latticeAut X₀ Y₀)).IsComplement'
      (b.basedAut.subgroupOf (P.latticeAut X₀ Y₀)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (Subgroup.disjoint_def.mpr fun hw hb ↦
    Subtype.ext <| Subgroup.disjoint_def.mp b.isComplement'_weylGroup_basedAut.disjoint hw hb) ?_
  refine Set.eq_univ_of_forall fun g ↦ let s := b.semidirectProductMulEquiv.symm (g : P.Aut); ?_
  exact Set.mem_mul.mpr ⟨⟨s.left, b.semidirectProductMulEquiv_symm_left_mem_latticeAut hW g⟩,
    s.left.property, ⟨s.right, b.semidirectProductMulEquiv_symm_right_mem_latticeAut hW g.property⟩,
    s.right.property, Subtype.ext (b.semidirectProductMulEquiv_symm_left_mul_right (g : P.Aut))⟩

/-- **Restricted semidirect product decomposition of `P.latticeAut X₀ Y₀`**: for a finite
reduced crystallographic pairing over a characteristic-zero domain and any submodule pair
`(X₀, Y₀)` with `P.weylGroup ≤ P.latticeAut X₀ Y₀` (in particular any dual lattice pair via
`IsDualLatticePair.weylGroup_le_latticeAut`), `P.latticeAut X₀ Y₀` is the semidirect product of
`P.weylGroup` by `↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)`. -/
noncomputable def latticeAutSemidirectProductMulEquiv :
    P.weylGroup ⋊[b.conjWeylGroupLatticeAut X₀ Y₀]
      ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) ≃* P.latticeAut X₀ Y₀ where
  toFun x := ⟨(x.left : P.Aut) * x.right, mul_mem (hW x.left.property) x.right.property.right⟩
  invFun g := let s := b.semidirectProductMulEquiv.symm (g : P.Aut)
    ⟨s.left, ⟨s.right, s.right.property,
      b.semidirectProductMulEquiv_symm_right_mem_latticeAut hW g.property⟩⟩
  left_inv x := by
    have h := b.semidirectProductMulEquiv_symm_mul x.left ⟨x.right, x.right.property.left⟩
    exact SemidirectProduct.ext (congrArg (fun z ↦ z.left) h)
      (Subtype.ext <| congrArg (fun z ↦ (z.right : P.Aut)) h)
  right_inv g := Subtype.ext (b.semidirectProductMulEquiv_symm_left_mul_right (g : P.Aut))
  map_mul' _ _ := Subtype.ext <| by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
      coe_conjWeylGroupLatticeAut_apply, mul_assoc, inv_mul_cancel_left]

/-- Coercing `b.latticeAutSemidirectProductMulEquiv hW x` to `P.Aut` multiplies its factors. -/
@[simp] theorem coe_latticeAutSemidirectProductMulEquiv_apply (x) :
    (b.latticeAutSemidirectProductMulEquiv hW x : P.Aut) = (x.left : P.Aut) * x.right := (rfl)

/-- The Weyl factor of `g : P.latticeAut X₀ Y₀` agrees with its Weyl factor in `P.Aut`. -/
@[simp] theorem latticeAutSemidirectProductMulEquiv_symm_left (g : P.latticeAut X₀ Y₀) :
    ((b.latticeAutSemidirectProductMulEquiv hW).symm g).left =
      (b.semidirectProductMulEquiv.symm (g : P.Aut)).left := (rfl)

/-- The based factor of `g : P.latticeAut X₀ Y₀` coerces to its based factor in `P.Aut`. -/
@[simp] theorem coe_latticeAutSemidirectProductMulEquiv_symm_right (g : P.latticeAut X₀ Y₀) :
    (((b.latticeAutSemidirectProductMulEquiv hW).symm g).right : P.Aut) =
      ((b.semidirectProductMulEquiv.symm (g : P.Aut)).right : P.Aut) := (rfl)

end WeylLeLatticeAut

/-- **For a spanning root system, a Cartan-matrix symmetry `σ` lifts to a based automorphism
preserving `(X₀, Y₀)` if and only if its canonical extension `b.equivOfCartanMatrixEq b σ hσ`
belongs to `P.latticeAut X₀ Y₀`.** -/
theorem exists_basedAut_inf_latticeAut_forall_indexEquiv_eq_iff [P.IsRootSystem] (b : P.Base)
    (X₀ : Submodule R M) (Y₀ : Submodule R N) (σ : Equiv.Perm b.support)
    (hσ : ∀ i j, b.cartanMatrix (σ i) (σ j) = b.cartanMatrix i j) :
    (∃ g : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀), ∀ i : b.support, (g : P.Aut).indexEquiv i = σ i) ↔
      b.equivOfCartanMatrixEq b σ hσ ∈ P.latticeAut X₀ Y₀ := by
  obtain ⟨δ₀, hδ₀, huniq⟩ := b.existsUnique_basedAut_of_cartanMatrix σ hσ
  have heq : (δ₀ : P.Aut) = b.equivOfCartanMatrixEq b σ hσ := congrArg Subtype.val
    (huniq ⟨_, mem_basedAut_iff_map_eq.mpr (TauCeti.map_equivOfCartanMatrixEq b b σ hσ)⟩
      (TauCeti.equivOfCartanMatrixEq_indexEquiv_apply b b σ hσ)).symm
  exact ⟨fun ⟨g, hg⟩ ↦ heq ▸ congrArg Subtype.val (huniq ⟨g.val, g.property.left⟩ hg) ▸
      g.property.right, fun hlat ↦ ⟨⟨δ₀, δ₀.property, heq ▸ hlat⟩, hδ₀⟩⟩

/-- When `b.equivOfCartanMatrixEq b σ hσ` preserves `(X₀, Y₀)`, there is a unique based
lattice-preserving automorphism inducing `σ` on the simple roots. -/
theorem existsUnique_basedAut_inf_latticeAut_of_cartanMatrix [P.IsRootSystem] (b : P.Base)
    {X₀ : Submodule R M} {Y₀ : Submodule R N} (σ : Equiv.Perm b.support)
    (hσ : ∀ i j, b.cartanMatrix (σ i) (σ j) = b.cartanMatrix i j)
    (hlat : b.equivOfCartanMatrixEq b σ hσ ∈ P.latticeAut X₀ Y₀) :
    ∃! g : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀),
      ∀ i : b.support, (g : P.Aut).indexEquiv i = σ i := by
  obtain ⟨g, hg⟩ := (b.exists_basedAut_inf_latticeAut_forall_indexEquiv_eq_iff X₀ Y₀ σ hσ).mpr hlat
  obtain ⟨_, -, huniq⟩ := b.existsUnique_basedAut_of_cartanMatrix σ hσ
  exact ⟨g, hg, fun g' hg' ↦ Subtype.ext <| congrArg (fun x : b.basedAut ↦ (x : P.Aut)) <|
    (huniq ⟨g'.val, g'.property.left⟩ hg').trans (huniq ⟨g.val, g.property.left⟩ hg).symm⟩

end Base

end LatticeSemidirect

end RootPairing
