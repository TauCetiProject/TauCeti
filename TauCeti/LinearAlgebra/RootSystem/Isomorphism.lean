/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.LinearAlgebra.RootSystem.DynkinType` is imported publicly: `TauCeti.HasCartanType`
-- occurs in the statement below, and `TauCeti.HasCartanType.exists_supportEquiv_cartanMatrix_eq`
-- supplies the relabelling the proof feeds to Mathlib's `RootPairing.Base.equivOfCartanMatrixEq`.
-- It re-exports `Mathlib.LinearAlgebra.RootSystem.CartanMatrix`, hence that theorem.
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.CoefficientReflection

/-!
# Root systems of the same Dynkin type are isomorphic

The Cartan-Killing classification has two halves. One is combinatorial: the Cartan matrix of a base
of an irreducible reduced crystallographic finite root system is, after relabelling the nodes, one
of the standard matrices `TauCeti.DynkinType.cartanMatrix`. The other is the rigidity statement
that the type is a complete invariant, and this file supplies it: two root systems carrying bases
of the same Dynkin type are isomorphic as root pairings.

For root systems over a common base ring, `TauCeti.nonempty_equiv_of_hasCartanType` applies
Mathlib's `RootPairing.Base.equivOfCartanMatrixEq` directly, with
`TauCeti.HasCartanType.exists_supportEquiv_cartanMatrix_eq` supplying the relabelling: two bases of
type `t` are each labelled by the nodes of `t`, and composing the two labellings identifies their
supports compatibly with the Cartan matrices.

Over arbitrary characteristic-zero domains and without `[IsRootSystem]`, a
Cartan-matrix-preserving bijection `e : b.support ≃ b₂.support` between the simple roots of two
finite reduced crystallographic root pairings extends via
`RootPairing.Base.indexEquivOfCartanMatrixEq` to a bijection `ι ≃ ι₂` between their root index
types. It relabels simple-root coordinates along `e.symm`, intertwines `P.rootSpanMem ℤ` with
`b.toWeightBasisInt.equiv b₂.toWeightBasisInt e`, and preserves root heights, positivity, the
positive roots, maximal root height (when the root sets are nonempty), and the highest root (when
`P₂` is irreducible).

## Main results

* `RootPairing.Base.indexEquivOfCartanMatrixEq`: bijection `ι ≃ ι₂` induced by a
  Cartan-matrix-preserving bijection of simple roots, without `[IsRootSystem]` or equal base rings,
  together with `rootCoefficients_indexEquivOfCartanMatrixEq`, `indexEquivOfCartanMatrixEq_symm`,
  `rootSpanMem_indexEquivOfCartanMatrixEq`, `indexEquivOfCartanMatrixEq_apply_support`,
  `height_indexEquivOfCartanMatrixEq`, `isPos_indexEquivOfCartanMatrixEq_iff`,
  `image_indexEquivOfCartanMatrixEq_posRoots`, `height_highestRoot_eq_of_cartanMatrixEq`, and
  `indexEquivOfCartanMatrixEq_highestRoot`.
* `TauCeti.equivOfCartanMatrixEq_indexEquiv_apply`: the isomorphism constructed from a Cartan
  matrix relabelling carries each simple-root index according to that relabelling.
* `TauCeti.map_equivOfCartanMatrixEq`: transporting the first base along that isomorphism gives
  the second base exactly.
* `TauCeti.nonempty_equiv_of_hasCartanType`: **two root systems carrying bases of the same Cartan
  type are isomorphic.**

## References

This file proves `nonempty_equiv_of_hasCartanType`. See Bourbaki, *Lie Groups and Lie Algebras,
Chapters 4-6*, chapter VI, §4, and Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §11.1, for the isomorphism theorem in the classical language.
-/

public section

namespace RootPairing.Base

section IndexEquiv

variable {ι R M N ι₂ R₂ M₂ N₂ : Type*}
  [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [CommRing R₂] [IsDomain R₂] [CharZero R₂]
  [AddCommGroup M₂] [Module R₂ M₂] [AddCommGroup N₂] [Module R₂ N₂]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  {P₂ : RootPairing ι₂ R₂ M₂ N₂} [Finite ι₂] [P₂.IsCrystallographic] [P₂.IsReduced]

private lemma comp_mem_range_rootCoefficients
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    b.rootCoefficients i ∘ e.symm ∈ Set.range b₂.rootCoefficients := by
  classical
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp
    (b.iUnion_orbit_single_eq_range_rootCoefficients.ge ⟨i, rfl⟩)
  rw [← b₂.iUnion_orbit_single_eq_range_rootCoefficients, Set.mem_iUnion]
  refine ⟨e k, ?_⟩
  have h := Matrix.comp_equiv_mem_orbit b.cartanMatrix b.cartanMatrix_apply_same
    b₂.cartanMatrix_apply_same e.symm (fun u v ↦ by simpa using he (e.symm u) (e.symm v)) hk
  have hs : (Pi.single k 1 : b.support → ℤ) ∘ e.symm = Pi.single (e k) 1 := by
    ext u; simp [Pi.single_apply, e.symm_apply_eq]
  rwa [hs] at h

/-- **A Cartan-matrix-preserving bijection between the simple roots of two finite reduced
crystallographic root pairings extends to a bijection between their root index types**, without
requiring `[IsRootSystem]` or equal ambient scalar rings. -/
noncomputable def indexEquivOfCartanMatrixEq
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) : ι ≃ ι₂ :=
  have hbij : Set.BijOn (· ∘ e.symm)
      (Set.range b.rootCoefficients) (Set.range b₂.rootCoefficients) :=
    ⟨by rintro _ ⟨i, rfl⟩; exact comp_mem_range_rootCoefficients b b₂ e he i,
     fun c₁ _ c₂ _ h ↦ funext fun k ↦ by simpa using congrFun h (e k),
     by rintro _ ⟨j, rfl⟩
        exact ⟨b₂.rootCoefficients j ∘ e,
          comp_mem_range_rootCoefficients b₂ b e.symm
            (fun u v ↦ by simpa using (he (e.symm u) (e.symm v)).symm) j,
          funext fun _ ↦ by simp⟩⟩
  (Equiv.ofInjective b.rootCoefficients b.rootCoefficients_injective).trans <|
    hbij.equiv.trans (Equiv.ofInjective b₂.rootCoefficients b₂.rootCoefficients_injective).symm

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` relabels simple-root coefficient columns along
`e.symm`. -/
@[simp]
theorem rootCoefficients_indexEquivOfCartanMatrixEq
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    b₂.rootCoefficients (b.indexEquivOfCartanMatrixEq b₂ e he i) =
      b.rootCoefficients i ∘ e.symm := by
  simp only [indexEquivOfCartanMatrixEq, Equiv.trans_apply]
  exact Equiv.apply_ofInjective_symm b₂.rootCoefficients_injective _

/-- The inverse of `RootPairing.Base.indexEquivOfCartanMatrixEq` is the equivalence induced by
`e.symm`. -/
@[simp]
theorem indexEquivOfCartanMatrixEq_symm
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    (b.indexEquivOfCartanMatrixEq b₂ e he).symm =
      b₂.indexEquivOfCartanMatrixEq b e.symm
        (fun u v ↦ by simpa using (he (e.symm u) (e.symm v)).symm) := by
  ext j
  apply b.rootCoefficients_injective
  rw [rootCoefficients_indexEquivOfCartanMatrixEq, Equiv.symm_symm]
  ext k
  have h := congrFun (rootCoefficients_indexEquivOfCartanMatrixEq b b₂ e he
    ((b.indexEquivOfCartanMatrixEq b₂ e he).symm j)) (e k)
  simpa using h.symm

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` intertwines `rootSpanMem ℤ` with the linear
equivalence `b.toWeightBasisInt.equiv b₂.toWeightBasisInt e` of root lattices. -/
@[simp]
theorem rootSpanMem_indexEquivOfCartanMatrixEq
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    P₂.rootSpanMem ℤ (b.indexEquivOfCartanMatrixEq b₂ e he i) =
      b.toWeightBasisInt.equiv b₂.toWeightBasisInt e (P.rootSpanMem ℤ i) := by
  have hspan : P.rootSpanMem ℤ i = ∑ k, b.rootCoefficients i k • b.toWeightBasisInt k :=
    Subtype.ext <| by
      dsimp only [RootPairing.rootSpanMem]
      rw [Submodule.coe_sum]
      simp_rw [SetLike.val_smul, b.coe_toWeightBasisInt_apply]
      exact (b.sum_rootCoefficients_smul_root i).symm
  rw [hspan, map_sum]
  apply Subtype.ext
  dsimp only [RootPairing.rootSpanMem]
  rw [Submodule.coe_sum, ← b₂.sum_rootCoefficients_smul_root]
  simp_rw [rootCoefficients_indexEquivOfCartanMatrixEq, Function.comp_apply, map_zsmul,
    Module.Basis.equiv_apply, SetLike.val_smul, b₂.coe_toWeightBasisInt_apply]
  exact (e.sum_comp fun u ↦ b.rootCoefficients i (e.symm u) • P₂.root u).symm.trans
    (Finset.sum_congr rfl fun k _ ↦ by simp)

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` extends `e` on simple-root indices. -/
@[simp]
theorem indexEquivOfCartanMatrixEq_apply_support
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : b.support) :
    b.indexEquivOfCartanMatrixEq b₂ e he i = e i := by
  classical
  apply b₂.rootCoefficients_injective
  rw [rootCoefficients_indexEquivOfCartanMatrixEq, b.rootCoefficients_coe i,
    b₂.rootCoefficients_coe (e i)]
  ext u; simp [Pi.single_apply, e.symm_apply_eq]

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` preserves root heights. -/
@[simp]
theorem height_indexEquivOfCartanMatrixEq
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    b₂.height (b.indexEquivOfCartanMatrixEq b₂ e he i) = b.height i := by
  rw [← b₂.sum_rootCoefficients_eq_height, rootCoefficients_indexEquivOfCartanMatrixEq,
    ← b.sum_rootCoefficients_eq_height]
  exact e.symm.sum_comp (b.rootCoefficients i)

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` preserves positivity of roots. -/
@[simp]
theorem isPos_indexEquivOfCartanMatrixEq_iff
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    b₂.IsPos (b.indexEquivOfCartanMatrixEq b₂ e he i) ↔ b.IsPos i := by
  rw [← b₂.zero_le_rootCoefficients_iff, ← b.zero_le_rootCoefficients_iff,
    rootCoefficients_indexEquivOfCartanMatrixEq]
  exact ⟨fun h k ↦ by simpa using h (e k), fun h u ↦ h (e.symm u)⟩

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` maps the positive roots of `b` onto the positive
roots of `b₂`. -/
@[simp]
theorem image_indexEquivOfCartanMatrixEq_posRoots
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    b.indexEquivOfCartanMatrixEq b₂ e he '' TauCeti.posRoots P b = TauCeti.posRoots P₂ b₂ := by
  rw [(b.indexEquivOfCartanMatrixEq b₂ e he).image_eq_preimage_symm]
  ext j
  simp [TauCeti.mem_posRoots]

/-- Bases of finite reduced crystallographic root pairings with equal Cartan matrices up to
relabelling have the same maximal root height. -/
theorem height_highestRoot_eq_of_cartanMatrixEq [Nonempty ι] [Nonempty ι₂]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    b.height b.highestRoot = b₂.height b₂.highestRoot := by
  refine le_antisymm ?_ ?_
  · rw [← height_indexEquivOfCartanMatrixEq b b₂ e he b.highestRoot]
    exact b₂.height_le_height_highestRoot _
  · have hsymm : ∀ u v, b.cartanMatrix (e.symm u) (e.symm v) = b₂.cartanMatrix u v :=
      fun u v ↦ by simpa using (he (e.symm u) (e.symm v)).symm
    rw [← height_indexEquivOfCartanMatrixEq b₂ b e.symm hsymm b₂.highestRoot]
    exact b.height_le_height_highestRoot _

/-- When `P₂` is irreducible, `RootPairing.Base.indexEquivOfCartanMatrixEq` sends the highest root
of `b` to the highest root of `b₂`. -/
@[simp]
theorem indexEquivOfCartanMatrixEq_highestRoot [Nonempty ι] [Nonempty ι₂] [P₂.IsIrreducible]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    b.indexEquivOfCartanMatrixEq b₂ e he b.highestRoot = b₂.highestRoot := by
  by_contra hne
  exact (b₂.height_lt_height_highestRoot hne).ne <|
    (height_indexEquivOfCartanMatrixEq b b₂ e he b.highestRoot).trans
      (height_highestRoot_eq_of_cartanMatrixEq b b₂ e he)

end IndexEquiv

end RootPairing.Base

namespace TauCeti

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
  [CharZero R] [IsDomain R] [Finite ι] [Finite ι₂]
  [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
  [P₂.IsRootSystem] [P₂.IsCrystallographic] [P₂.IsReduced]

/-- The root-index equivalence constructed from a relabelling of equal Cartan matrices restricts
to that relabelling on the chosen simple roots.

Mathlib constructs the equivalence on all root indices by transporting the roots through the
linear equivalence between the two simple-root bases. This theorem exposes the resulting value on
a simple root, so consumers do not have to unfold that construction. -/
@[simp] theorem equivOfCartanMatrixEq_indexEquiv_apply (b : P.Base) (b₂ : P₂.Base)
    (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j)
    (i : b.support) :
    (b.equivOfCartanMatrixEq b₂ e he).indexEquiv i = e i := by
  apply P₂.root.injective
  rw [← (b.equivOfCartanMatrixEq b₂ e he).root_weightMap_apply]
  -- Expose the basis equivalence used internally by `equivOfCartanMatrixEq`; its public
  -- `Basis.equiv_apply` equation then identifies the image without unfolding either basis.
  change b.toWeightBasis.equiv b₂.toWeightBasis e (P.root i) = P₂.root (e i)
  rw [← b.toWeightBasis_apply i, Module.Basis.equiv_apply, b₂.toWeightBasis_apply]

/-- The covariant inverse coweight equivalence constructed from equal Cartan matrices sends a
chosen simple coroot to the simple coroot selected by the supplied relabelling. -/
@[simp] theorem equivOfCartanMatrixEq_coweightEquiv_symm_apply_coroot
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j)
    (i : b.support) :
    (_root_.RootPairing.Equiv.coweightEquiv
      (b.equivOfCartanMatrixEq b₂ e he)).symm (P.coroot i) = P₂.coroot (e i) := by
  let E := b.equivOfCartanMatrixEq b₂ e he
  have hindex : E.indexEquiv.symm (e i) = i := by
    rw [← equivOfCartanMatrixEq_indexEquiv_apply b b₂ e he i]
    exact E.indexEquiv.symm_apply_apply i
  apply (_root_.RootPairing.Equiv.coweightEquiv E).injective
  rw [LinearEquiv.apply_symm_apply, _root_.RootPairing.Equiv.coweightEquiv_apply]
  simpa only [hindex] using
    (_root_.RootPairing.Hom.coroot_coweightMap_apply P P₂ (e i) E.toHom).symm

/-- Transporting a base along the root-system equivalence constructed from equal Cartan matrices
gives the target base exactly. Thus the construction remembers the supplied simple-root
relabelling as an equivalence of based root systems. -/
@[simp] theorem map_equivOfCartanMatrixEq (b : P.Base) (b₂ : P₂.Base)
    (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    b.map (b.equivOfCartanMatrixEq b₂ e he) = b₂ := by
  classical
  apply RootPairing.Base.ext
  rw [b.support_map_eq]
  ext j
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [equivOfCartanMatrixEq_indexEquiv_apply b b₂ e he ⟨i, hi⟩]
    exact (e ⟨i, hi⟩).property
  · intro hj
    let i := e.symm ⟨j, hj⟩
    refine ⟨i, i.property, ?_⟩
    simp [i]

/-- **Two root systems carrying bases of the same Cartan type are isomorphic.** This is the
rigidity half of the Cartan-Killing classification: the Dynkin type is not merely an invariant of a
finite reduced crystallographic root system, it is a complete one.

Only the existence of an isomorphism is asserted. The isomorphism produced depends on the two
labellings of the supports by the nodes of `t`, which `TauCeti.HasCartanType` quantifies
existentially, so there is no canonical choice to name; a caller that needs one destructures the two
`HasCartanType` witnesses and applies `RootPairing.Base.equivOfCartanMatrixEq` itself. -/
theorem nonempty_equiv_of_hasCartanType (b : P.Base) (b₂ : P₂.Base) (t : DynkinType)
    (h : HasCartanType P b t) (h₂ : HasCartanType P₂ b₂ t) :
    Nonempty (P.Equiv P₂) :=
  let ⟨e, he⟩ := h.exists_supportEquiv_cartanMatrix_eq h₂
  ⟨_root_.RootPairing.Base.equivOfCartanMatrixEq b b₂ e he⟩

end TauCeti
