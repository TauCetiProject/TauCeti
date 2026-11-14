/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseChange
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Lattice
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut
import TauCeti.LinearAlgebra.RootSystem.Isomorphism
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Bases, based automorphisms, central directions, and dual isogeny lattices

This file connects the based automorphism theory of `TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut`
with scalar extension (`RootPairing.baseChange`) and restriction to dual isogeny lattices
(`RootPairing.IsDualLatticePair.restrict`):

1. **Scalar extension and lattice restriction of bases.** Extending a base `b : P.Base` along a
   faithful flat algebra `S` gives `b.baseChange S : (P.baseChange S).Base` with the same simple
   indices and Cartan matrix. Conversely, restricting a base of `P` to a dual `R`-lattice pair
   `(X₀, Y₀)` gives `hXY.restrictBase b : hXY.restrict.Base`, identifying the based automorphisms
   of `hXY.restrict` with `↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)` when `X₀` and `Y₀` are base-change
   lattices (`IsDualLatticePair.basedAutMulEquiv`). On the unit-tensor lattices `1 ⊗ X` and
   `1 ⊗ Y`, extending and restricting recovers `b` along `unitTmulRootPairingEquiv`.
2. **Restricted semidirect product for dual isogeny lattices.** Because `P.weylGroup` stabilizes
   every dual lattice pair (`IsDualLatticePair.weylGroup_le_latticeAut`), the ambient semidirect
   decomposition `W ⋊ b.basedAut ≃* P.Aut` restricts to
   `P.weylGroup ⋊ ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) ≃* P.latticeAut X₀ Y₀`
   (`Base.latticeAutSemidirectProductMulEquiv`). For a spanning ambient pairing, Cartan-matrix
   symmetries lift to `↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)` precisely when their unique ambient
   extension preserves `(X₀, Y₀)`.
3. **Common coroot kernel and the cylinder chamber.** For a balanced root pairing `P`, the root
   span `P.rootSpan R` and the common coroot kernel `⨅ i, LinearMap.ker (P.coroot' i)` are
   complementary (`isCompl_rootSpan_iInf_ker_coroot'`), yielding the projection `P.rootSpanProj`.
   Over an ordered field `K`, the preimage under `P.rootSpanProj` of the open dominant chamber of
   `P.restrictScalars' K` in `P.rootSpan K` is the **open cylinder chamber**
   `b.openCylinderChamber`; for a finite reduced crystallographic pairing `D` with finite free
   coweights, its scalar-extended cylinder chamber in `K ⊗[R] X` is preserved by
   `D.autBaseChangeHom K g` if and only if `g ∈ b.basedAut`
   (`Base.mem_basedAut_iff_smul_openCylinderChamber`).
4. **Central automorphisms and root-free data.** Every base stabilizer contains the kernel
   `(Equiv.indexHom P).ker` of compatible central automorphisms (`Equiv.ofFixRootCoroot`). When
   `ι` is empty, `P.weylGroup = ⊥`, `b.basedAut = ⊤`, and `P.Aut ≃* (M ≃ₗ[R] M)`
   (`autMulEquivOfIsEmpty`); on the rank-2 root-free integral datum
   `RootPairing.empty ℤ (Fin 2 → ℤ)` the unipotent shear makes `basedAut` infinite
   (`infinite_basedAut_empty_fin_two`).

## Main definitions

* `RootPairing.Base.baseChange`: scalar extension of a base along a faithful flat algebra.
* `RootPairing.IsDualLatticePair.restrictBase` and `RootPairing.IsDualLatticePair.basedAutMulEquiv`:
  restriction of a base to dual lattices and the isomorphism
  `(hXY.restrictBase b).basedAut ≃* ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)`.
* `RootPairing.Base.latticeAutSemidirectProductMulEquiv`: the restricted semidirect product
  `P.weylGroup ⋊ ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) ≃* P.latticeAut X₀ Y₀`.
* `RootPairing.rootSpanProj`, `RootPairing.Base.cylinderChamber`, and
  `RootPairing.Base.openCylinderChamber`: projection onto `rootSpan` along `⨅ i, ker (coroot' i)`
  and the closed/open cylinder chambers.
* `RootPairing.Equiv.ofFixRootCoroot`, `RootPairing.autMulEquivOfIsEmpty`, and `RootPairing.empty`:
  compatible central automorphisms and root-free pairings.

## Main results

* `RootPairing.Base.isComplement'_weylGroup_basedAut_subgroupOf`: the Weyl group complements the
  based lattice stabilizer inside `P.latticeAut X₀ Y₀`.
* `RootPairing.Base.exists_mem_basedAut_inf_latticeAut_iff`: criterion for a Cartan-matrix symmetry
  to preserve a dual lattice pair.
* `RootPairing.Base.mem_basedAut_iff_smul_openCylinderChamber`: an automorphism of a full datum is
  based if and only if its scalar extension preserves the open cylinder chamber.
* `RootPairing.infinite_basedAut_empty_fin_two`: `b.basedAut` can be infinite for a finite reduced
  crystallographic integral root pairing.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7,
  and 7.4.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C,
  C.43, C.51, and C.53.
-/

public section

open Function Module Pointwise Set TensorProduct

namespace RootPairing

/-! ### Scalar extension of a base -/

section BaseBaseChange

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

namespace Base

variable (b : P.Base) (S : Type*) [CommRing S] [Algebra R S] [FaithfulSMul R S] [Flat R S]
  [Free R N] [Module.Finite R N]

/-- **Extension of scalars of a base** along a faithful flat algebra `S`, keeping the same simple
root indices `b.support`. Flatness preserves linear independence of simple roots and coroots, while
the additive monoid closures of `1 ⊗ αᵢ` and `1 ⊗ αᵢ∨` are the images of those over `R`. -/
noncomputable def baseChange : (P.baseChange S).Base where
  support := b.support
  linearIndepOn_root := by
    have h : (fun x : (b.support : Set ι) ↦ (P.baseChange S).root x) =
        fun x : (b.support : Set ι) ↦ (1 : S) ⊗ₜ[R] P.root x :=
      funext fun x ↦ P.baseChange_root S x
    rw [LinearIndepOn, h]
    exact Module.Flat.linearIndependent_one_tmul (S := S) b.linearIndepOn_root
  linearIndepOn_coroot := by
    have h : (fun x : (b.support : Set ι) ↦ (P.baseChange S).coroot x) =
        fun x : (b.support : Set ι) ↦ (1 : S) ⊗ₜ[R] P.coroot x :=
      funext fun x ↦ P.baseChange_coroot S x
    rw [LinearIndepOn, h]
    exact Module.Flat.linearIndependent_one_tmul (S := S) b.linearIndepOn_coroot
  root_mem_or_neg_mem i := by
    let f := (TensorProduct.mk R S M 1).toAddMonoidHom
    have himg : (P.baseChange S).root '' (b.support : Set ι) = f '' (P.root '' b.support) := by
      rw [← image_comp]
      exact congrArg (· '' _) (funext (P.baseChange_root S))
    rw [himg, ← AddMonoidHom.map_mclosure, P.baseChange_root S i]
    rcases b.root_mem_or_neg_mem i with h | h
    · exact .inl ⟨P.root i, h, rfl⟩
    · exact .inr ⟨-P.root i, h, map_neg f (P.root i)⟩
  coroot_mem_or_neg_mem i := by
    let f := (TensorProduct.mk R S N 1).toAddMonoidHom
    have himg : (P.baseChange S).coroot '' (b.support : Set ι) = f '' (P.coroot '' b.support) := by
      rw [← image_comp]
      exact congrArg (· '' _) (funext (P.baseChange_coroot S))
    rw [himg, ← AddMonoidHom.map_mclosure, P.baseChange_coroot S i]
    rcases b.coroot_mem_or_neg_mem i with h | h
    · exact .inl ⟨P.coroot i, h, rfl⟩
    · exact .inr ⟨-P.coroot i, h, map_neg f (P.coroot i)⟩

/-- Scalar extension of a base leaves `support` unchanged. -/
@[simp]
theorem support_baseChange : (b.baseChange S).support = b.support :=
  (rfl)

/-- Transporting `b.baseChange S` by `P.autBaseChangeHom S g` agrees with
`(b.map g).baseChange S`. -/
@[simp]
theorem map_autBaseChangeHom (g : P.Aut) :
    (b.baseChange S).map (P.autBaseChangeHom S g) = (b.map g).baseChange S := by
  classical
  exact Base.ext_iff.mpr (by simp [Base.support_map_eq])

/-- Scalar extension preserves and reflects membership in `basedAut`. -/
theorem autBaseChangeHom_mem_basedAut_iff {g : P.Aut} :
    P.autBaseChangeHom S g ∈ (b.baseChange S).basedAut ↔ g ∈ b.basedAut := by
  simp [Base.mem_basedAut_iff]

/-- Scalar extension preserves every entry of the `T`-valued Cartan matrix of a base. -/
@[simp]
theorem cartanMatrixIn_baseChange_apply (T : Type*) [CommRing T] [Algebra T R] [Algebra T S]
    [IsScalarTower T R S] [FaithfulSMul T S] [P.IsValuedIn T]
    (i j : (b.baseChange S).support) :
    (b.baseChange S).cartanMatrixIn T i j =
      b.cartanMatrixIn T ⟨i, (b.support_baseChange S).le i.2⟩
        ⟨j, (b.support_baseChange S).le j.2⟩ :=
  P.baseChange_pairingIn S T i j

/-- Scalar extension preserves every entry of the integral Cartan matrix of a crystallographic root
pairing. -/
theorem cartanMatrix_baseChange_apply [CharZero S] [P.IsCrystallographic]
    (i j : (b.baseChange S).support) :
    (b.baseChange S).cartanMatrix i j =
      b.cartanMatrix ⟨i, (b.support_baseChange S).le i.2⟩
        ⟨j, (b.support_baseChange S).le j.2⟩ :=
  b.cartanMatrixIn_baseChange_apply S ℤ i j

end Base

end BaseBaseChange

/-! ### Pullback and lattice restriction of bases and based automorphisms -/

section BaseComap

variable {ι R S M₀ N₀ M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
  [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

namespace Base

/-- If `f : M₀ →ₗ[R] M` is an `R`-linear map into an `S`-module over a faithful `R`-algebra `S`
sending `v₀` to an `S`-linearly independent family `v` on `s`, then `v₀` is `R`-linearly independent
on `s`. -/
theorem linearIndepOn_of_comp_eq {s : Set ι} {v₀ : ι → M₀} {v : ι → M}
    (hv : LinearIndepOn S v s) (f : M₀ →ₗ[R] M) (hcomp_eq : ∀ i, f (v₀ i) = v i) :
    LinearIndepOn R v₀ s := by
  have hcomp : (f ∘ v₀ ∘ ((↑) : s → ι)) = (v ∘ ((↑) : s → ι)) := funext fun x ↦ hcomp_eq x
  have hli : LinearIndependent R (f ∘ v₀ ∘ ((↑) : s → ι)) := by
    rw [hcomp]
    exact hv.linearIndependent.restrict_scalars <| by
      simp_rw [← Algebra.algebraMap_eq_smul_one]
      exact FaithfulSMul.algebraMap_injective R S
  exact hli.of_comp

/-- If `f : M₀ →+ M` is an injective additive homomorphism sending `v₀` to `v`, then
positive/negative additive-monoid-closure membership of `v i` over `v '' s` pulls back to `v₀ i`
over `v₀ '' s`. -/
theorem mem_closure_or_neg_mem_of_injective {s : Set ι} {v₀ : ι → M₀} {v : ι → M} {i : ι}
    (hv : v i ∈ AddSubmonoid.closure (v '' s) ∨ -v i ∈ AddSubmonoid.closure (v '' s))
    (f : M₀ →+ M) (hf : Injective f) (hcomp_eq : ∀ j, f (v₀ j) = v j) :
    v₀ i ∈ AddSubmonoid.closure (v₀ '' s) ∨ -v₀ i ∈ AddSubmonoid.closure (v₀ '' s) := by
  have himg : f '' (v₀ '' s) = v '' s := by
    rw [← image_comp]
    exact congrArg (· '' s) (funext hcomp_eq)
  rcases hv with h | h
  · rw [← himg, ← AddMonoidHom.map_mclosure] at h
    obtain ⟨z, hz, hzeq⟩ := h
    exact .inl (hf (hzeq.trans (hcomp_eq i).symm) ▸ hz)
  · rw [← himg, ← AddMonoidHom.map_mclosure] at h
    obtain ⟨z, hz, hzeq⟩ := h
    have hzeq' : f z = f (-v₀ i) := by
      rw [map_neg, hcomp_eq i]
      exact hzeq
    exact .inr (hf hzeq' ▸ hz)

/-- **Pullback of a base `b : P.Base`** along injective `R`-linear maps `fM : M₀ →ₗ[R] M` and
`fN : N₀ →ₗ[R] N` over a faithful `R`-algebra `S` compatible with roots and coroots. -/
noncomputable def comapOfInjective {P₀ : RootPairing ι R M₀ N₀} {P : RootPairing ι S M N}
    (b : P.Base) (fM : M₀ →ₗ[R] M) (fN : N₀ →ₗ[R] N) (hfM : Injective fM) (hfN : Injective fN)
    (hroot : ∀ i, fM (P₀.root i) = P.root i) (hcoroot : ∀ i, fN (P₀.coroot i) = P.coroot i) :
    P₀.Base where
  support := b.support
  linearIndepOn_root := linearIndepOn_of_comp_eq (S := S) b.linearIndepOn_root fM hroot
  linearIndepOn_coroot := linearIndepOn_of_comp_eq (S := S) b.linearIndepOn_coroot fN hcoroot
  root_mem_or_neg_mem i := mem_closure_or_neg_mem_of_injective (b.root_mem_or_neg_mem i)
    fM.toAddMonoidHom hfM hroot
  coroot_mem_or_neg_mem i := mem_closure_or_neg_mem_of_injective (b.coroot_mem_or_neg_mem i)
    fN.toAddMonoidHom hfN hcoroot

/-- `Base.comapOfInjective` leaves `support` unchanged. -/
@[simp]
theorem support_comapOfInjective {P₀ : RootPairing ι R M₀ N₀} {P : RootPairing ι S M N}
    (b : P.Base) (fM : M₀ →ₗ[R] M) (fN : N₀ →ₗ[R] N) (hfM : Injective fM) (hfN : Injective fN)
    (hroot : ∀ i, fM (P₀.root i) = P.root i) (hcoroot : ∀ i, fN (P₀.coroot i) = P.coroot i) :
    (b.comapOfInjective fM fN hfM hfN hroot hcoroot).support = b.support :=
  (rfl)

end Base

end BaseComap

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
@[simp]
theorem support_restrictBase (b : P.Base) : (hXY.restrictBase b).support = b.support :=
  (rfl)

/-- Lattice restriction of bases commutes with transporting by `hXY.restrictAutHom`. -/
@[simp]
theorem map_restrictAutHom (b : P.Base) (g : P.latticeAut X₀ Y₀) :
    (hXY.restrictBase b).map (hXY.restrictAutHom g) = hXY.restrictBase (b.map (g : P.Aut)) := by
  classical
  exact Base.ext_iff.mpr (by simp [Base.support_map_eq])

/-- A restricted automorphism fixes `hXY.restrictBase b` if and only if the ambient automorphism
fixes `b`. -/
theorem restrictAutHom_mem_basedAut_iff (b : P.Base) {g : P.latticeAut X₀ Y₀} :
    hXY.restrictAutHom g ∈ (hXY.restrictBase b).basedAut ↔ (g : P.Aut) ∈ b.basedAut := by
  simp [Base.mem_basedAut_iff]

/-- Lattice restriction preserves every entry of the `T`-valued Cartan matrix of a base. -/
theorem cartanMatrixIn_restrictBase_apply (b : P.Base) (T : Type*) [CommRing T] [Algebra T R]
    [Algebra T S] [IsScalarTower T R S] [FaithfulSMul T S] [P.IsValuedIn T]
    (i j : (hXY.restrictBase b).support) :
    letI := hXY.isValuedIn_restrict T
    (hXY.restrictBase b).cartanMatrixIn T i j =
      b.cartanMatrixIn T ⟨i, (hXY.support_restrictBase b).le i.2⟩
        ⟨j, (hXY.support_restrictBase b).le j.2⟩ :=
  hXY.restrict_pairingIn T i j

section BaseChangeLattices

variable [Free R Y₀] [Module.Finite R Y₀]
  (hX : IsBaseChange S X₀.subtype) (hY : IsBaseChange S Y₀.subtype)

/-- Extending an integral automorphism preserves `b` if and only if the integral automorphism
preserves `hXY.restrictBase b`. -/
theorem extendAutHom_mem_basedAut_iff (b : P.Base) {u : hXY.restrict.Aut} :
    (hXY.extendAutHom hX hY u : P.Aut) ∈ b.basedAut ↔ u ∈ (hXY.restrictBase b).basedAut := by
  simp [Base.mem_basedAut_iff]

include hX hY in
/-- **Scalar extension and lattice restriction identify `(hXY.restrictBase b).basedAut` with the
based lattice-preserving automorphisms `↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)`.** -/
noncomputable def basedAutMulEquiv (b : P.Base) :
    (hXY.restrictBase b).basedAut ≃* ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) where
  toFun u := ⟨(hXY.extendAutHom hX hY u : P.Aut),
    (hXY.extendAutHom_mem_basedAut_iff hX hY b).mpr u.2, (hXY.extendAutHom hX hY u).2⟩
  invFun g := ⟨hXY.restrictAutHom ⟨g.1, g.2.2⟩,
    (hXY.restrictAutHom_mem_basedAut_iff b).mpr g.2.1⟩
  left_inv u := Subtype.ext (hXY.restrictAutHom_extendAutHom hX hY u)
  right_inv g := Subtype.ext <| by
    have h := hXY.extendAutHom_restrictAutHom hX hY ⟨g.1, g.2.2⟩
    exact congrArg (fun x : P.latticeAut X₀ Y₀ ↦ (x : P.Aut)) h
  map_mul' u v := Subtype.ext <| by
    have h := map_mul (hXY.extendAutHom hX hY) (u : hXY.restrict.Aut) (v : hXY.restrict.Aut)
    exact congrArg (fun x : P.latticeAut X₀ Y₀ ↦ (x : P.Aut)) h

/-- Coercing `hXY.basedAutMulEquiv hX hY b u` to `P.Aut` applies `hXY.extendAutHom hX hY`. -/
@[simp]
theorem coe_basedAutMulEquiv_apply (b : P.Base) (u : (hXY.restrictBase b).basedAut) :
    (hXY.basedAutMulEquiv hX hY b u : P.Aut) = hXY.extendAutHom hX hY u :=
  (rfl)

/-- Coercing `(hXY.basedAutMulEquiv hX hY b).symm g` to `hXY.restrict.Aut` applies
`hXY.restrictAutHom`. -/
@[simp]
theorem coe_basedAutMulEquiv_symm_apply (b : P.Base)
    (g : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)) :
    ((hXY.basedAutMulEquiv hX hY b).symm g : hXY.restrict.Aut) =
      hXY.restrictAutHom ⟨g.1, g.2.2⟩ :=
  (rfl)

end BaseChangeLattices

end IsDualLatticePair

/-- Extending a base `b : D.Base` to `D.baseChange S` and restricting to the unit-tensor lattices
`1 ⊗ X` and `1 ⊗ Y` recovers `b` transported along `D.unitTmulRootPairingEquiv S`. -/
@[simp]
theorem restrictBase_baseChange {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (D : RootPairing ι R X Y) [Flat R S]
    [Free R Y] [Module.Finite R Y] (b : D.Base) :
    (D.isDualLatticePair_range_mk_one S).restrictBase (b.baseChange S) =
      b.map (D.unitTmulRootPairingEquiv S) := by
  classical
  exact Base.ext_iff.mpr (by simp [Base.support_map_eq])

end LatticeBase

/-! ### Restricted semidirect product for dual isogeny lattices -/

section LatticeSemidirect

variable {ι R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module S M] [Module R M]
  [AddCommGroup N] [Module S N] [Module R N]
  {P : RootPairing ι S M N}

namespace Base

/-- Conjugation action of the based lattice-preserving automorphisms
`↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)` on `P.weylGroup`, obtained by restricting `b.conjWeylGroup`. -/
noncomputable def conjWeylGroupLatticeAut (b : P.Base)
    (X₀ : Submodule R M) (Y₀ : Submodule R N) :
    ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) →* MulAut P.weylGroup :=
  b.conjWeylGroup.comp (Subgroup.inclusion inf_le_left)

/-- A based lattice-preserving automorphism `δ` acts on `P.weylGroup` by `w ↦ δ w δ⁻¹`. -/
@[simp]
theorem coe_conjWeylGroupLatticeAut_apply (b : P.Base) (X₀ : Submodule R M) (Y₀ : Submodule R N)
    (δ : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)) (w : P.weylGroup) :
    (b.conjWeylGroupLatticeAut X₀ Y₀ δ w : P.Aut) = (δ : P.Aut) * w * (δ : P.Aut)⁻¹ :=
  b.coe_conjWeylGroup_apply ⟨δ.1, δ.2.1⟩ w

variable [Finite ι] [CharZero S] [IsDomain S] [P.IsCrystallographic] [P.IsReduced]

section DualLatticePair

variable [Algebra R S] [FaithfulSMul R S] [IsScalarTower R S M] [IsScalarTower R S N]

/-- **The Weyl group complements the based automorphisms inside `P.latticeAut X₀ Y₀`** for every
dual lattice pair `(X₀, Y₀)`. -/
theorem isComplement'_weylGroup_basedAut_subgroupOf (b : P.Base)
    {X₀ : Submodule R M} {Y₀ : Submodule R N} (hXY : P.IsDualLatticePair X₀ Y₀) :
    (P.weylGroup.subgroupOf (P.latticeAut X₀ Y₀)).IsComplement'
      (b.basedAut.subgroupOf (P.latticeAut X₀ Y₀)) := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · refine Subgroup.disjoint_def.mpr fun {g} hw hb ↦ Subtype.ext ?_
    exact Subgroup.disjoint_def.mp b.isComplement'_weylGroup_basedAut.disjoint hw hb
  · refine Set.eq_univ_of_forall fun g ↦ ?_
    let s := b.semidirectProductMulEquiv.symm (g : P.Aut)
    have hW : (s.left : P.Aut) ∈ P.latticeAut X₀ Y₀ := hXY.weylGroup_le_latticeAut s.left.2
    have hδ : (s.right : P.Aut) ∈ P.latticeAut X₀ Y₀ := by
      rw [b.coe_semidirectProductMulEquiv_symm_right]
      exact mul_mem (inv_mem hW) g.2
    refine Set.mem_mul.mpr ⟨⟨s.left, hW⟩, s.left.2, ⟨s.right, hδ⟩, s.right.2, ?_⟩
    exact Subtype.ext (b.semidirectProductMulEquiv_symm_left_mul_right (g : P.Aut))

/-- **Restricted semidirect product decomposition of `P.latticeAut X₀ Y₀`**: for a finite reduced
crystallographic pairing over a characteristic-zero domain and any dual lattice pair `(X₀, Y₀)`,
`P.latticeAut X₀ Y₀` is the semidirect product of `P.weylGroup` by
`↥(b.basedAut ⊓ P.latticeAut X₀ Y₀)`. -/
noncomputable def latticeAutSemidirectProductMulEquiv (b : P.Base)
    {X₀ : Submodule R M} {Y₀ : Submodule R N} (hXY : P.IsDualLatticePair X₀ Y₀) :
    P.weylGroup ⋊[b.conjWeylGroupLatticeAut X₀ Y₀] ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀) ≃*
      P.latticeAut X₀ Y₀ where
  toFun x := ⟨(x.left : P.Aut) * x.right,
    mul_mem (hXY.weylGroup_le_latticeAut x.left.2) x.right.2.2⟩
  invFun g :=
    let s := b.semidirectProductMulEquiv.symm (g : P.Aut)
    have hW : (s.left : P.Aut) ∈ P.latticeAut X₀ Y₀ := hXY.weylGroup_le_latticeAut s.left.2
    ⟨s.left, ⟨s.right, s.right.2, by
      rw [b.coe_semidirectProductMulEquiv_symm_right]
      exact (P.latticeAut X₀ Y₀).mul_mem ((P.latticeAut X₀ Y₀).inv_mem hW) g.2⟩⟩
  left_inv x := by
    have h := b.semidirectProductMulEquiv_symm_mul x.left ⟨x.right, x.right.2.1⟩
    have hl := congrArg (fun z ↦ z.left) h
    have hr := congrArg (fun z ↦ (z.right : P.Aut)) h
    exact SemidirectProduct.ext hl (Subtype.ext hr)
  right_inv g := Subtype.ext (b.semidirectProductMulEquiv_symm_left_mul_right (g : P.Aut))
  map_mul' x y := Subtype.ext <| by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul,
      coe_conjWeylGroupLatticeAut_apply, mul_assoc, inv_mul_cancel_left]

/-- Coercing `b.latticeAutSemidirectProductMulEquiv hXY x` to `P.Aut` multiplies its two factors. -/
@[simp]
theorem coe_latticeAutSemidirectProductMulEquiv_apply (b : P.Base)
    {X₀ : Submodule R M} {Y₀ : Submodule R N} (hXY : P.IsDualLatticePair X₀ Y₀) (x) :
    (b.latticeAutSemidirectProductMulEquiv hXY x : P.Aut) = (x.left : P.Aut) * x.right :=
  (rfl)

/-- The Weyl factor of `g : P.latticeAut X₀ Y₀` agrees with its Weyl factor in `P.Aut`. -/
@[simp]
theorem latticeAutSemidirectProductMulEquiv_symm_left (b : P.Base)
    {X₀ : Submodule R M} {Y₀ : Submodule R N} (hXY : P.IsDualLatticePair X₀ Y₀)
    (g : P.latticeAut X₀ Y₀) :
    ((b.latticeAutSemidirectProductMulEquiv hXY).symm g).left =
      (b.semidirectProductMulEquiv.symm (g : P.Aut)).left :=
  (rfl)

/-- The based factor of `g : P.latticeAut X₀ Y₀` coerces to its based factor in `P.Aut`. -/
@[simp]
theorem coe_latticeAutSemidirectProductMulEquiv_symm_right (b : P.Base)
    {X₀ : Submodule R M} {Y₀ : Submodule R N} (hXY : P.IsDualLatticePair X₀ Y₀)
    (g : P.latticeAut X₀ Y₀) :
    (((b.latticeAutSemidirectProductMulEquiv hXY).symm g).right : P.Aut) =
      ((b.semidirectProductMulEquiv.symm (g : P.Aut)).right : P.Aut) :=
  (rfl)

end DualLatticePair

/-- **For a spanning root system, a Cartan-matrix symmetry `σ` lifts to a based automorphism
preserving `(X₀, Y₀)` if and only if its canonical extension `b.equivOfCartanMatrixEq b σ hσ`
belongs to `P.latticeAut X₀ Y₀`.** -/
theorem exists_mem_basedAut_inf_latticeAut_iff [P.IsRootSystem] (b : P.Base)
    (X₀ : Submodule R M) (Y₀ : Submodule R N) (σ : Equiv.Perm b.support)
    (hσ : ∀ i j, b.cartanMatrix (σ i) (σ j) = b.cartanMatrix i j) :
    (∃ g : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀), ∀ i : b.support, (g : P.Aut).indexEquiv i = σ i) ↔
      b.equivOfCartanMatrixEq b σ hσ ∈ P.latticeAut X₀ Y₀ := by
  obtain ⟨δ₀, hδ₀, huniq⟩ := b.existsUnique_basedAut_of_cartanMatrix σ hσ
  have heq : (δ₀ : P.Aut) = b.equivOfCartanMatrixEq b σ hσ := by
    have hmem : b.equivOfCartanMatrixEq b σ hσ ∈ b.basedAut :=
      mem_basedAut_iff_map_eq.mpr (TauCeti.map_equivOfCartanMatrixEq b b σ hσ)
    exact congrArg (fun x : b.basedAut ↦ (x : P.Aut))
      (huniq ⟨_, hmem⟩ (TauCeti.equivOfCartanMatrixEq_indexEquiv_apply b b σ hσ)).symm
  refine ⟨?_, fun hlat ↦ ⟨⟨δ₀, δ₀.2, heq ▸ hlat⟩, hδ₀⟩⟩
  rintro ⟨g, hg⟩
  have hgδ : (⟨g.1, g.2.1⟩ : b.basedAut) = δ₀ := huniq ⟨g.1, g.2.1⟩ hg
  have hval : (g : P.Aut) = (δ₀ : P.Aut) := congrArg (fun x : b.basedAut ↦ (x : P.Aut)) hgδ
  exact heq ▸ hval ▸ g.2.2

/-- When `b.equivOfCartanMatrixEq b σ hσ` preserves `(X₀, Y₀)`, there is a unique based
lattice-preserving automorphism inducing `σ` on the simple roots. -/
theorem existsUnique_mem_basedAut_inf_latticeAut_of_cartanMatrix [P.IsRootSystem] (b : P.Base)
    {X₀ : Submodule R M} {Y₀ : Submodule R N} (σ : Equiv.Perm b.support)
    (hσ : ∀ i j, b.cartanMatrix (σ i) (σ j) = b.cartanMatrix i j)
    (hlat : b.equivOfCartanMatrixEq b σ hσ ∈ P.latticeAut X₀ Y₀) :
    ∃! g : ↥(b.basedAut ⊓ P.latticeAut X₀ Y₀),
      ∀ i : b.support, (g : P.Aut).indexEquiv i = σ i := by
  obtain ⟨g, hg⟩ := (b.exists_mem_basedAut_inf_latticeAut_iff X₀ Y₀ σ hσ).mpr hlat
  obtain ⟨_, -, huniq⟩ := b.existsUnique_basedAut_of_cartanMatrix σ hσ
  refine ⟨g, hg, fun g' hg' ↦ Subtype.ext ?_⟩
  exact congrArg (fun x : b.basedAut ↦ (x : P.Aut))
    ((huniq ⟨g'.1, g'.2.1⟩ hg').trans (huniq ⟨g.1, g.2.1⟩ hg).symm)

end Base

end LatticeSemidirect

/-! ### Common coroot kernel projection and the cylinder chamber -/

section CylinderChamber

section Balanced

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N) [P.IsBalanced]

/-- **In a balanced root pairing, `P.rootSpan R` and the common coroot kernel
`⨅ i, LinearMap.ker (P.coroot' i)` are complementary submodules of `M`.** -/
theorem isCompl_rootSpan_iInf_ker_coroot' :
    IsCompl (P.rootSpan R) (⨅ i, LinearMap.ker (P.coroot' i)) :=
  P.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot' ▸ IsBalanced.isPerfectCompl.isCompl_left

/-- **Linear projection onto `P.rootSpan R` along the common coroot kernel
`⨅ i, LinearMap.ker (P.coroot' i)`.** -/
noncomputable def rootSpanProj : M →ₗ[R] P.rootSpan R :=
  (P.rootSpan R).projectionOnto (⨅ i, LinearMap.ker (P.coroot' i))
    P.isCompl_rootSpan_iInf_ker_coroot'

/-- `P.rootSpanProj` acts as the identity on `P.rootSpan R`. -/
@[simp]
theorem rootSpanProj_apply_of_mem (x : P.rootSpan R) :
    P.rootSpanProj x = x :=
  Submodule.projectionOnto_apply_left _ x

/-- The kernel of `P.rootSpanProj` is the common coroot kernel
`⨅ i, LinearMap.ker (P.coroot' i)`. -/
@[simp]
theorem ker_rootSpanProj :
    LinearMap.ker P.rootSpanProj = ⨅ i, LinearMap.ker (P.coroot' i) :=
  Submodule.ker_projectionOnto _

/-- `P.rootSpanProj x = 0` if and only if every coroot functional vanishes on `x`. -/
@[simp]
theorem rootSpanProj_eq_zero_iff {x : M} :
    P.rootSpanProj x = 0 ↔ ∀ i, P.coroot' i x = 0 := by
  rw [rootSpanProj, Submodule.projectionOnto_apply_eq_zero_iff, Submodule.mem_iInf]
  rfl

/-- Projecting to `P.rootSpan R` along the common coroot kernel preserves pairing with every
coroot. -/
@[simp]
theorem toLinearMap_coe_rootSpanProj_coroot (x : M) (i : ι) :
    P.toLinearMap (P.rootSpanProj x : M) (P.coroot i) = P.toLinearMap x (P.coroot i) := by
  have hmem : x - (P.rootSpanProj x : M) ∈ ⨅ j, LinearMap.ker (P.coroot' j) :=
    Submodule.sub_projection_mem P.isCompl_rootSpan_iInf_ker_coroot' x
  have hi : P.coroot' i (x - (P.rootSpanProj x : M)) = 0 :=
    LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hmem i)
  rw [map_sub, sub_eq_zero] at hi
  exact hi.symm

-- Not `@[simp]`: `coroot'` is an `abbrev` for `toLinearMap.flip (coroot i)`, so
-- `toLinearMap_coe_rootSpanProj_coroot` is the `simp`-normal form.
/-- Projecting to `P.rootSpan R` along the common coroot kernel preserves every coroot functional
`P.coroot' i`. -/
theorem coroot'_coe_rootSpanProj (i : ι) (x : M) :
    P.coroot' i (P.rootSpanProj x : M) = P.coroot' i x :=
  P.toLinearMap_coe_rootSpanProj_coroot x i

/-- `P.rootSpanProj` is equivariant for the weight action of `P.Aut`. -/
theorem coe_rootSpanProj_smul (g : P.Aut) (x : M) :
    (P.rootSpanProj (g • x) : M) = g • (P.rootSpanProj x : M) := by
  have hrootSpan : g • (P.rootSpanProj x : M) ∈ P.rootSpan R := by
    refine Submodule.span_induction ?_ (by simp)
      (fun u v _ _ hu hv ↦ by rw [smul_add]; exact add_mem hu hv)
      (fun r u _ hu ↦ by
        -- `g • (r • u)` is `g.weightEquiv (r • u) = r • g.weightEquiv u`.
        change g.weightEquiv (r • u) ∈ P.rootSpan R
        rw [map_smul]
        exact Submodule.smul_mem _ r hu) (P.rootSpanProj x).2
    rintro _ ⟨j, rfl⟩
    rw [← Equiv.root_indexEquiv_eq_smul]
    exact Submodule.subset_span (mem_range_self (g.indexEquiv j))
  have hsub_span : (P.rootSpanProj (g • x) : M) - g • (P.rootSpanProj x : M) ∈ P.rootSpan R :=
    sub_mem (P.rootSpanProj (g • x)).2 hrootSpan
  have hsub_ker :
      (P.rootSpanProj (g • x) : M) - g • (P.rootSpanProj x : M) ∈
        ⨅ i, LinearMap.ker (P.coroot' i) := by
    refine (Submodule.mem_iInf _).mpr fun i ↦ LinearMap.mem_ker.mpr ?_
    rw [map_sub, P.coroot'_coe_rootSpanProj, coroot'_smul, coroot'_smul,
      P.coroot'_coe_rootSpanProj, sub_self]
  exact sub_eq_zero.mp <|
    Submodule.disjoint_def.mp P.isCompl_rootSpan_iInf_ker_coroot'.disjoint _ hsub_span hsub_ker

end Balanced

section RestrictScalarsBase

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
  {P : RootPairing ι L M N}

/-- **Restriction of scalars of a base** along `RootPairing.restrictScalars'`, keeping the same
simple indices `b.support`. -/
noncomputable def Base.restrictScalars' (b : P.Base) (K : Type*) [Field K] [Algebra K L]
    [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
    [P.IsBalanced] [P.IsValuedIn K] : (P.restrictScalars' K).Base :=
  b.comapOfInjective (Submodule.span K (range P.root)).subtype
    (Submodule.span K (range P.coroot)).subtype Subtype.val_injective Subtype.val_injective
    (P.restrictScalars_coe_root K) (P.restrictScalars_coe_coroot K)

/-- `Base.restrictScalars'` leaves `support` unchanged. -/
@[simp]
theorem Base.support_restrictScalars' (b : P.Base) (K : Type*) [Field K] [Algebra K L]
    [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
    [P.IsBalanced] [P.IsValuedIn K] :
    (b.restrictScalars' K).support = b.support :=
  (rfl)

end RestrictScalarsBase

section FieldCylinder

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] {P : RootPairing ι K M N} [P.IsBalanced]

/-- Evaluating a coroot functional of `P.restrictScalars' K` on `P.rootSpanProj x` recovers
`P.coroot' i x`. -/
theorem restrictScalars'_coroot'_rootSpanProj (i : ι) (x : M) :
    (P.restrictScalars' K).coroot' i (P.rootSpanProj x) = P.coroot' i x := by
  have h := P.restrictScalars_toLinearMap_apply_apply K (P.rootSpanProj x)
    ((P.restrictScalars' K).coroot i)
  rw [Algebra.algebraMap_self, RingHom.id_apply, P.restrictScalars_coe_coroot] at h
  exact h.trans (P.coroot'_coe_rootSpanProj i x)

namespace Base

variable (b : P.Base) [Preorder K]

/-- **The closed cylinder chamber** of a balanced root pairing over a preordered field: the inverse
image under `P.rootSpanProj` (projection along the common coroot kernel) of the closed dominant
chamber in the root-span root system `P.restrictScalars' K`. -/
noncomputable def cylinderChamber : Set M :=
  P.rootSpanProj ⁻¹' dominantChamber (P.restrictScalars' K) (b.restrictScalars' K)

/-- **The open cylinder chamber** of a balanced root pairing over a preordered field: the inverse
image under `P.rootSpanProj` (projection along the common coroot kernel) of the open dominant
chamber in the root-span root system `P.restrictScalars' K`. -/
noncomputable def openCylinderChamber : Set M :=
  P.rootSpanProj ⁻¹' openDominantChamber (P.restrictScalars' K) (b.restrictScalars' K)

/-- The closed cylinder chamber coincides with `dominantChamber P b`. -/
theorem cylinderChamber_eq_dominantChamber :
    b.cylinderChamber = dominantChamber P b := by
  ext x
  simp only [cylinderChamber, mem_preimage, mem_dominantChamber, Base.support_restrictScalars']
  exact forall₂_congr fun i _ ↦ by rw [restrictScalars'_coroot'_rootSpanProj]

/-- The open cylinder chamber coincides with `openDominantChamber P b`. -/
theorem openCylinderChamber_eq_openDominantChamber :
    b.openCylinderChamber = openDominantChamber P b := by
  ext x
  simp only [openCylinderChamber, mem_preimage, mem_openDominantChamber,
    Base.support_restrictScalars']
  exact forall₂_congr fun i _ ↦ by rw [restrictScalars'_coroot'_rootSpanProj]

end Base

end FieldCylinder

section DatumCylinder

variable {ι R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
  [AddCommGroup Y] [Module R Y] (D : RootPairing ι R X Y)
  [Finite ι] [D.IsCrystallographic] [Free R Y] [Module.Finite R Y]

/-- Scalar extension of a finite crystallographic root pairing to a characteristic-zero field is
balanced (`rootSpan` and `corootSpan` are perfectly complementary). -/
theorem isBalanced_baseChange_of_field (K : Type*) [Field K] [CharZero K]
    [Algebra R K] [FaithfulSMul R K] : (D.baseChange K).IsBalanced := by
  cases nonempty_fintype ι
  infer_instance

/-- **An automorphism of a finite reduced crystallographic root datum is based if and only if its
scalar extension to an ordered field `K` (such as `ℚ` or `ℝ`) preserves the open cylinder chamber**
(the preimage of the root-span chamber under projection along the common coroot kernel). -/
theorem Base.mem_basedAut_iff_smul_openCylinderChamber [D.IsReduced] (b : D.Base)
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Algebra R K] [FaithfulSMul R K] [Flat R K] {g : D.Aut} :
    letI := D.isBalanced_baseChange_of_field K
    g ∈ b.basedAut ↔
      D.autBaseChangeHom K g • (b.baseChange K).openCylinderChamber =
        (b.baseChange K).openCylinderChamber := by
  let _ : (D.baseChange K).IsBalanced := D.isBalanced_baseChange_of_field K
  have _ : (D.baseChange K).flip.IsReduced := (D.baseChange K).flip_isReduced
  rw [← b.autBaseChangeHom_mem_basedAut_iff K,
    (b.baseChange K).mem_basedAut_iff_smul_openDominantChamber,
    (b.baseChange K).openCylinderChamber_eq_openDominantChamber]

end DatumCylinder

end CylinderChamber

/-! ### Compatible central automorphisms, root-free pairings, and infinite `basedAut` -/

section CentralAndEmpty

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- An automorphism belongs to `(Equiv.indexHom P).ker` if and only if it fixes every root. -/
theorem mem_ker_indexHom_iff {g : P.Aut} :
    g ∈ (Equiv.indexHom P).ker ↔ ∀ i, g • P.root i = P.root i := by
  rw [MonoidHom.mem_ker, Equiv.indexHom_apply, _root_.Equiv.ext_iff]
  refine forall_congr' fun i ↦ ?_
  rw [Equiv.Perm.one_apply, ← P.root.injective.eq_iff, Equiv.root_indexEquiv_eq_smul]

/-- An automorphism in `(Equiv.indexHom P).ker` preserves every coroot functional. -/
theorem coroot'_smul_of_mem_ker_indexHom {g : P.Aut} (hg : g ∈ (Equiv.indexHom P).ker)
    (i : ι) (x : M) : P.coroot' i (g • x) = P.coroot' i x := by
  have h1 : g.indexEquiv = 1 := hg
  rw [coroot'_smul, ← Equiv.Perm.inv_def, h1, inv_one, Equiv.Perm.one_apply]

/-- **Every base stabilizer contains the kernel `(Equiv.indexHom P).ker` of central
automorphisms.** -/
theorem Base.ker_indexHom_le_basedAut {P : RootPairing ι R M N} (b : P.Base) :
    (Equiv.indexHom P).ker ≤ b.basedAut := fun g hg ↦ by
  have h1 : g.indexEquiv = 1 := hg
  simp [Base.mem_basedAut_iff, h1]

/-- **Compatible central automorphism** attached to any linear automorphism `e : M ≃ₗ[R] M` that
fixes every root and preserves every coroot functional (equivalently `e x - x` lies in the common
coroot kernel `⨅ i, ker (P.coroot' i)`). No direct-sum splitting of `M` is assumed. -/
noncomputable def Equiv.ofFixRootCoroot (e : M ≃ₗ[R] M)
    (hroot : ∀ i, e (P.root i) = P.root i)
    (hcoroot : ∀ i x, P.coroot' i (e x) = P.coroot' i x) : P.Aut :=
  let eN : N ≃ₗ[R] N := P.flip.toPerfPair ≪≫ₗ e.dualMap ≪≫ₗ P.flip.toPerfPair.symm
  { weightMap := e.toLinearMap
    coweightMap := eN.toLinearMap
    indexEquiv := _root_.Equiv.refl ι
    weight_coweight_transpose := by
      ext y x
      simp [eN]
    root_weightMap := funext hroot
    coroot_coweightMap := funext fun i ↦ P.flip.toPerfPair.injective <| LinearMap.ext fun x ↦ by
      simpa [eN, coroot'] using hcoroot i x
    bijective_weightMap := e.bijective
    bijective_coweightMap := eN.bijective }

/-- The weight equivalence of `Equiv.ofFixRootCoroot` is `e`. -/
@[simp]
theorem Equiv.ofFixRootCoroot_weightEquiv (e : M ≃ₗ[R] M)
    (hroot : ∀ i, e (P.root i) = P.root i)
    (hcoroot : ∀ i x, P.coroot' i (e x) = P.coroot' i x) :
    (Equiv.ofFixRootCoroot P e hroot hcoroot).weightEquiv = e :=
  LinearEquiv.toLinearMap_injective rfl

/-- `Equiv.ofFixRootCoroot` acts trivially on the root indices. -/
@[simp]
theorem Equiv.ofFixRootCoroot_indexEquiv (e : M ≃ₗ[R] M)
    (hroot : ∀ i, e (P.root i) = P.root i)
    (hcoroot : ∀ i x, P.coroot' i (e x) = P.coroot' i x) :
    (Equiv.ofFixRootCoroot P e hroot hcoroot).indexEquiv = _root_.Equiv.refl ι :=
  (rfl)

/-- Every `Equiv.ofFixRootCoroot` lies in `(Equiv.indexHom P).ker`. -/
theorem Equiv.ofFixRootCoroot_mem_ker_indexHom (e : M ≃ₗ[R] M)
    (hroot : ∀ i, e (P.root i) = P.root i)
    (hcoroot : ∀ i x, P.coroot' i (e x) = P.coroot' i x) :
    Equiv.ofFixRootCoroot P e hroot hcoroot ∈ (Equiv.indexHom P).ker :=
  MonoidHom.mem_ker.mpr (Equiv.ofFixRootCoroot_indexEquiv P e hroot hcoroot)

/-- Every compatible central automorphism `Equiv.ofFixRootCoroot` belongs to `b.basedAut`. -/
theorem Equiv.ofFixRootCoroot_mem_basedAut (b : P.Base) (e : M ≃ₗ[R] M)
    (hroot : ∀ i, e (P.root i) = P.root i)
    (hcoroot : ∀ i x, P.coroot' i (e x) = P.coroot' i x) :
    Equiv.ofFixRootCoroot P e hroot hcoroot ∈ b.basedAut :=
  b.ker_indexHom_le_basedAut (Equiv.ofFixRootCoroot_mem_ker_indexHom P e hroot hcoroot)

/-- The weight-space image of `(Equiv.indexHom P).ker` consists of the linear automorphisms of `M`
fixing every root and preserving every coroot functional. -/
theorem map_weightHom_ker_indexHom :
    (((Equiv.indexHom P).ker.map (Equiv.weightHom P)) : Set (M ≃ₗ[R] M)) =
      {e : M ≃ₗ[R] M |
        (∀ i, e (P.root i) = P.root i) ∧ ∀ i x, P.coroot' i (e x) = P.coroot' i x} := by
  ext e
  simp only [Subgroup.coe_map, mem_image, SetLike.mem_coe, Set.mem_ofPred_eq]
  refine ⟨?_, fun ⟨hr, hc⟩ ↦ ⟨Equiv.ofFixRootCoroot P e hr hc,
    Equiv.ofFixRootCoroot_mem_ker_indexHom P e hr hc,
    Equiv.ofFixRootCoroot_weightEquiv P e hr hc⟩⟩
  rintro ⟨g, hg, rfl⟩
  exact ⟨(P.mem_ker_indexHom_iff.mp hg), P.coroot'_smul_of_mem_ker_indexHom hg⟩

section IsEmpty

variable [IsEmpty ι]

/-- **A root-free pairing has trivial Weyl group.** -/
@[simp]
theorem weylGroup_eq_bot_of_isEmpty : P.weylGroup = ⊥ := by
  simp [weylGroup, range_eq_empty]

/-- **The unique base of a root-free pairing**, with empty support. -/
def Base.ofIsEmpty : P.Base where
  support := ∅
  linearIndepOn_root := by simp
  linearIndepOn_coroot := by simp
  root_mem_or_neg_mem := isEmptyElim
  coroot_mem_or_neg_mem := isEmptyElim

/-- The empty base has empty support. -/
@[simp]
theorem Base.support_ofIsEmpty : (Base.ofIsEmpty P).support = ∅ :=
  (rfl)

/-- **Every automorphism of a root-free pairing is based.** -/
@[simp]
theorem Base.basedAut_eq_top_of_isEmpty {P : RootPairing ι R M N} (b : P.Base) :
    b.basedAut = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ b.ker_indexHom_le_basedAut (Subsingleton.elim (Equiv.indexHom P g) 1)

/-- **For a root-free pairing, `Equiv.weightHom` is a group isomorphism `P.Aut ≃* (M ≃ₗ[R] M)`.** -/
noncomputable def autMulEquivOfIsEmpty : P.Aut ≃* (M ≃ₗ[R] M) where
  toFun := Equiv.weightHom P
  invFun e := Equiv.ofFixRootCoroot P e isEmptyElim isEmptyElim
  left_inv g := Equiv.weightHom_injective P (Equiv.ofFixRootCoroot_weightEquiv P g.weightEquiv _ _)
  right_inv e := Equiv.ofFixRootCoroot_weightEquiv P e _ _
  map_mul' := map_mul (Equiv.weightHom P)

/-- `autMulEquivOfIsEmpty` acts via `Equiv.weightHom`. -/
@[simp]
theorem autMulEquivOfIsEmpty_apply (g : P.Aut) :
    P.autMulEquivOfIsEmpty g = g.weightEquiv :=
  (rfl)

/-- Every root-free pairing is vacuously reduced. -/
instance instIsReducedOfIsEmpty : P.IsReduced :=
  ⟨isEmptyElim⟩

/-- Every root-free pairing is vacuously valued in any base ring `S` (in particular,
crystallographic when `S = ℤ`). -/
instance instIsValuedInOfIsEmpty (S : Type*) [CommRing S] [Algebra S R] : P.IsValuedIn S :=
  ⟨isEmptyElim⟩

/-- Every root-free pairing is vacuously balanced (`rootSpan R = ⊥` and `corootSpan R = ⊥`). -/
instance instIsBalancedOfIsEmpty : P.IsBalanced where
  isPerfectCompl :=
    { isCompl_left := by
        simpa [rootSpan, corootSpan, range_eq_empty,
          LinearMap.range_eq_top.mpr P.toPerfPair.symm.surjective] using isCompl_bot_top
      isCompl_right := by
        simpa [rootSpan, corootSpan, range_eq_empty,
          LinearMap.range_eq_top.mpr P.flip.toPerfPair.symm.surjective] using isCompl_bot_top }

end IsEmpty

/-- **The canonical root-free pairing** on a reflexive `R`-module `M` and its dual
`Module.Dual R M`. -/
def empty (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] :
    RootPairing Empty R M (Module.Dual R M) where
  toLinearMap := Module.Dual.eval R M
  root := ⟨Empty.elim, fun x ↦ x.elim⟩
  coroot := ⟨Empty.elim, fun x ↦ x.elim⟩
  root_coroot_two x := x.elim
  reflectionPerm x := x.elim
  reflectionPerm_root x := x.elim
  reflectionPerm_coroot x := x.elim

/-- **The based automorphism group of a finite reduced crystallographic integral root datum can be
infinite**: on the rank-2 root-free datum `RootPairing.empty ℤ (Fin 2 → ℤ)`, the unipotent shear
`(x₀, x₁) ↦ (x₀ + x₁, x₁)` generates infinitely many based automorphisms. -/
theorem infinite_basedAut_empty_fin_two :
    Infinite (Base.ofIsEmpty (RootPairing.empty ℤ (Fin 2 → ℤ))).basedAut := by
  let P₀ := RootPairing.empty ℤ (Fin 2 → ℤ)
  let shear : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    { toFun v := ![v 0 + v 1, v 1]
      invFun v := ![v 0 - v 1, v 1]
      left_inv v := by ext i; fin_cases i <;> simp
      right_inv v := by ext i; fin_cases i <;> simp
      map_add' u v := by ext i; fin_cases i <;> simp [add_add_add_comm]
      map_smul' r v := by ext i; fin_cases i <;> simp [mul_add] }
  have hpow (n : ℕ) : (shear ^ n) ![0, 1] = ![(n : ℤ), 1] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih]
      ext i
      fin_cases i <;> simp [shear]
  let f : ℕ → (Base.ofIsEmpty P₀).basedAut := fun n ↦
    ⟨P₀.autMulEquivOfIsEmpty.symm (shear ^ n), by simp⟩
  refine Infinite.of_injective f fun m n hmn ↦ ?_
  have heq : shear ^ m = shear ^ n :=
    P₀.autMulEquivOfIsEmpty.symm.injective (congrArg Subtype.val hmn)
  have h0 := congrArg (fun e : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) ↦ e ![0, 1] 0) heq
  rw [hpow m, hpow n] at h0
  exact Int.ofNat.inj h0

end CentralAndEmpty

end RootPairing
