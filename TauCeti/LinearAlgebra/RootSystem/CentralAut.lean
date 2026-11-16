/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Empty
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Central automorphisms of root pairings

Without a spanning assumption, `RootPairing.Equiv.indexHom P : P.Aut →* Equiv.Perm ι` can have a
nontrivial kernel. This file characterizes `(Equiv.indexHom P).ker` as the group of linear
automorphisms of `M` fixing every root and preserving every coroot functional, and identifies
`P.Aut ≃* (M ≃ₗ[R] M)` when `ι` is empty.

## Main definitions

* `RootPairing.Equiv.ofFixRootCoroot`: builds an automorphism in `(Equiv.indexHom P).ker` from any
  `e : M ≃ₗ[R] M` fixing every root and preserving every coroot functional.
* `RootPairing.autMulEquivOfIsEmpty`: `P.Aut ≃* (M ≃ₗ[R] M)` for `[IsEmpty ι]`.

## Main results

* `RootPairing.mem_ker_indexHom_iff`, `RootPairing.coroot'_smul_of_mem_ker_indexHom`, and
  `RootPairing.map_weightHom_ker_indexHom`: characterizations of `(Equiv.indexHom P).ker`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C, C.53.
-/

public section

namespace RootPairing

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

section OfFixRootCoroot

variable (e : M ≃ₗ[R] M) (hroot : ∀ i, e (P.root i) = P.root i)
  (hcoroot : ∀ i x, P.coroot' i (e x) = P.coroot' i x)

/-- **Compatible central automorphism** attached to any linear automorphism `e : M ≃ₗ[R] M` that
fixes every root and preserves every coroot functional (equivalently `e x - x` lies in the common
coroot kernel `⨅ i, ker (P.coroot' i)`). No direct-sum splitting of `M` is assumed. -/
noncomputable def Equiv.ofFixRootCoroot : P.Aut :=
  let eN : N ≃ₗ[R] N := P.flip.toPerfPair ≪≫ₗ e.dualMap ≪≫ₗ P.flip.toPerfPair.symm
  { weightMap := e.toLinearMap
    coweightMap := eN.toLinearMap
    indexEquiv := _root_.Equiv.refl ι
    weight_coweight_transpose := by ext y x; simp [eN]
    root_weightMap := funext hroot
    coroot_coweightMap := funext fun i ↦ P.flip.toPerfPair.injective <| LinearMap.ext fun x ↦ by
      simpa [eN, coroot'] using hcoroot i x
    bijective_weightMap := e.bijective
    bijective_coweightMap := eN.bijective }

/-- The weight equivalence of `Equiv.ofFixRootCoroot` is `e`. -/
@[simp] theorem Equiv.ofFixRootCoroot_weightEquiv :
    (Equiv.ofFixRootCoroot P e hroot hcoroot).weightEquiv = e :=
  LinearEquiv.toLinearMap_injective rfl

/-- The coweight equivalence of `Equiv.ofFixRootCoroot` is the transpose of `e` transported across
`P.flip.toPerfPair`. -/
@[simp] theorem Equiv.ofFixRootCoroot_coweightEquiv :
    (Equiv.ofFixRootCoroot P e hroot hcoroot).coweightEquiv =
      P.flip.toPerfPair ≪≫ₗ e.dualMap ≪≫ₗ P.flip.toPerfPair.symm :=
  LinearEquiv.toLinearMap_injective rfl

/-- The coweight equivalence of `Equiv.ofFixRootCoroot` is the adjoint of `e` with respect to
`P.toLinearMap`.

Not a `simp` lemma: `simp` derives this from `RootPairing.Equiv.ofFixRootCoroot_coweightEquiv`. -/
theorem Equiv.toLinearMap_ofFixRootCoroot_coweightEquiv (x : M) (y : N) :
    P.toLinearMap x ((Equiv.ofFixRootCoroot P e hroot hcoroot).coweightEquiv y) =
      P.toLinearMap (e x) y := by simp

/-- `Equiv.ofFixRootCoroot` acts trivially on the root indices. -/
@[simp] theorem Equiv.ofFixRootCoroot_indexEquiv :
    (Equiv.ofFixRootCoroot P e hroot hcoroot).indexEquiv = _root_.Equiv.refl ι := (rfl)

/-- Every `Equiv.ofFixRootCoroot` lies in `(Equiv.indexHom P).ker`. -/
theorem Equiv.ofFixRootCoroot_mem_ker_indexHom :
    Equiv.ofFixRootCoroot P e hroot hcoroot ∈ (Equiv.indexHom P).ker :=
  MonoidHom.mem_ker.mpr (Equiv.ofFixRootCoroot_indexEquiv P e hroot hcoroot)

end OfFixRootCoroot

/-- The weight-space image of `(Equiv.indexHom P).ker` consists of the linear automorphisms of `M`
fixing every root and preserving every coroot functional. -/
theorem map_weightHom_ker_indexHom :
    (((Equiv.indexHom P).ker.map (Equiv.weightHom P)) : Set (M ≃ₗ[R] M)) =
      {e : M ≃ₗ[R] M |
        (∀ i, e (P.root i) = P.root i) ∧ ∀ i x, P.coroot' i (e x) = P.coroot' i x} := by
  ext e
  simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq]
  exact ⟨by rintro ⟨g, hg, rfl⟩; exact ⟨P.mem_ker_indexHom_iff.mp hg,
      P.coroot'_smul_of_mem_ker_indexHom hg⟩,
    fun ⟨hr, hc⟩ ↦ ⟨Equiv.ofFixRootCoroot P e hr hc,
      Equiv.ofFixRootCoroot_mem_ker_indexHom P e hr hc,
      Equiv.ofFixRootCoroot_weightEquiv P e hr hc⟩⟩

/-- **For a root-free pairing, `Equiv.weightHom` is a group isomorphism
`P.Aut ≃* (M ≃ₗ[R] M)`.** -/
noncomputable def autMulEquivOfIsEmpty [IsEmpty ι] : P.Aut ≃* (M ≃ₗ[R] M) where
  toFun := Equiv.weightHom P
  invFun e := Equiv.ofFixRootCoroot P e isEmptyElim isEmptyElim
  left_inv g := Equiv.weightHom_injective P (Equiv.ofFixRootCoroot_weightEquiv P g.weightEquiv _ _)
  right_inv e := Equiv.ofFixRootCoroot_weightEquiv P e _ _
  map_mul' := map_mul (Equiv.weightHom P)

/-- `autMulEquivOfIsEmpty` acts via `Equiv.weightHom`. -/
@[simp] theorem autMulEquivOfIsEmpty_apply [IsEmpty ι] (g : P.Aut) :
    P.autMulEquivOfIsEmpty g = g.weightEquiv := (rfl)

/-- The inverse of `autMulEquivOfIsEmpty` lifts `e : M ≃ₗ[R] M` with weight equivalence `e`. -/
@[simp] theorem autMulEquivOfIsEmpty_symm_apply_weightEquiv [IsEmpty ι] (e : M ≃ₗ[R] M) :
    (P.autMulEquivOfIsEmpty.symm e).weightEquiv = e :=
  Equiv.ofFixRootCoroot_weightEquiv P e isEmptyElim isEmptyElim

end RootPairing
