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
-- `TauCeti.LinearAlgebra.RootSystem.Height` supplies `RootPairing.Base.ext`, used in a proof only.
import TauCeti.LinearAlgebra.RootSystem.Height
import TauCeti.LinearAlgebra.RootSystem.Span

/-!
# Root systems of the same Dynkin type are isomorphic

The Cartan-Killing classification has two halves. One is combinatorial: the Cartan matrix of a base
of an irreducible reduced crystallographic finite root system is, after relabelling the nodes, one
of the standard matrices `TauCeti.DynkinType.cartanMatrix`. The other is the rigidity statement
that the type is a complete invariant, and this file supplies it: two root systems carrying bases
of the same Dynkin type are isomorphic as root pairings.

Nothing here re-proves rigidity. Mathlib's `RootPairing.Base.equivOfCartanMatrixEq` already builds
an isomorphism from a relabelling matching the two Cartan matrices, and
`TauCeti.HasCartanType.exists_supportEquiv_cartanMatrix_eq` is what supplies such a relabelling: two
bases of type `t` are each labelled by the nodes of `t`, and composing the two labellings identifies
their supports compatibly with the Cartan matrices.

Without `[IsRootSystem]` or equal ambient base rings, the same simple-root basis comparison over `ℤ`
still identifies the root lattices `P.rootSpan ℤ ≃ₗ[ℤ] P₂.rootSpan ℤ` and restricts to a bijection
`RootPairing.Base.indexEquivOfCartanMatrixEq : ι ≃ ι₂` between root index types.

## Main results

* `RootPairing.Base.indexEquivOfCartanMatrixEq`: bijection `ι ≃ ι₂` induced by a
  Cartan-matrix-preserving bijection of simple roots, without `[IsRootSystem]` or equal base rings.
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
  {P₂ : RootPairing ι₂ R₂ M₂ N₂} [P₂.IsCrystallographic]

omit [IsDomain R] [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
private lemma toWeightBasisInt_eq_rootSpanMem (b : P.Base) (i : b.support) :
    b.toWeightBasisInt i = P.rootSpanMem ℤ i :=
  Subtype.ext (b.coe_toWeightBasisInt_apply i)

omit [IsDomain R₂] [CharZero R₂] in
private lemma apply_rootSpanMem_mem_range_of_cartanMatrixEq
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (f : P.rootSpan ℤ ≃ₗ[ℤ] P₂.rootSpan ℤ)
    (hf : ∀ i : b.support, f (P.rootSpanMem ℤ i) = P₂.rootSpanMem ℤ (e i))
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    f (P.rootSpanMem ℤ i) ∈ Set.range (P₂.rootSpanMem ℤ) := by
  have hcomm : ∀ k : b.support,
      f.toLinearMap.comp (P.reflectionRootSpan ℤ k).toLinearMap =
        (P₂.reflectionRootSpan ℤ (e k)).toLinearMap.comp f.toLinearMap := fun k =>
    b.toWeightBasisInt.ext fun j => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, toWeightBasisInt_eq_rootSpanMem, hf,
        P.reflectionRootSpan_rootSpanMem_eq_sub ℤ, P₂.reflectionRootSpan_rootSpanMem_eq_sub ℤ,
        map_sub, map_zsmul, ← b.cartanMatrixIn_def ℤ, ← b₂.cartanMatrixIn_def ℤ, he]
  refine b.induction_reflect i
    (p := fun idx => f (P.rootSpanMem ℤ idx) ∈ Set.range (P₂.rootSpanMem ℤ)) ?_
    (fun j hj => ⟨e ⟨j, hj⟩, (hf ⟨j, hj⟩).symm⟩) ?_
  · rintro j ⟨l, hl⟩
    exact ⟨P₂.reflectionPerm l l, by
      rw [P.rootSpanMem_reflectionPerm_self ℤ, map_neg, ← hl,
        P₂.rootSpanMem_reflectionPerm_self ℤ]⟩
  · rintro j k ⟨l, hl⟩ hk
    have hstep := LinearMap.congr_fun (hcomm ⟨k, hk⟩) (P.rootSpanMem ℤ j)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, reflectionRootSpan_rootSpanMem,
      ← hl] at hstep
    exact ⟨P₂.reflectionPerm (e ⟨k, hk⟩) l, hstep.symm⟩

/-- **A Cartan-matrix-preserving bijection between the simple roots of two finite reduced
crystallographic root pairings extends to a bijection between their root index types**, without
requiring `[IsRootSystem]` or equal ambient scalar rings. -/
noncomputable def indexEquivOfCartanMatrixEq [Finite ι₂] [P₂.IsReduced]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) : ι ≃ ι₂ :=
  let f : P.rootSpan ℤ ≃ₗ[ℤ] P₂.rootSpan ℤ := b.toWeightBasisInt.equiv b₂.toWeightBasisInt e
  have hf_supp : ∀ i : b.support, f (P.rootSpanMem ℤ i) = P₂.rootSpanMem ℤ (e i) := fun i => by
    simp [f, ← toWeightBasisInt_eq_rootSpanMem]
  have hbij : Set.BijOn f (Set.range (P.rootSpanMem ℤ)) (Set.range (P₂.rootSpanMem ℤ)) :=
    ⟨by rintro _ ⟨i, rfl⟩
        exact apply_rootSpanMem_mem_range_of_cartanMatrixEq b b₂ e f hf_supp he i,
     f.injective.injOn,
     by rintro y ⟨j, rfl⟩
        obtain ⟨i, hi⟩ := apply_rootSpanMem_mem_range_of_cartanMatrixEq b₂ b e.symm f.symm
          (fun i => f.injective (by simp [hf_supp])) (fun u v => by simp [(he _ _).symm]) j
        exact ⟨P.rootSpanMem ℤ i, Set.mem_range_self i, by rw [hi, f.apply_symm_apply]⟩⟩
  (Equiv.ofInjective (P.rootSpanMem ℤ) (P.rootSpanMem_injective ℤ)).trans <|
    hbij.equiv.trans (Equiv.ofInjective (P₂.rootSpanMem ℤ) (P₂.rootSpanMem_injective ℤ)).symm

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` intertwines `rootSpanMem ℤ` with the linear
equivalence `b.toWeightBasisInt.equiv b₂.toWeightBasisInt e` of root lattices. -/
@[simp]
theorem rootSpanMem_indexEquivOfCartanMatrixEq [Finite ι₂] [P₂.IsReduced]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : ι) :
    P₂.rootSpanMem ℤ (b.indexEquivOfCartanMatrixEq b₂ e he i) =
      b.toWeightBasisInt.equiv b₂.toWeightBasisInt e (P.rootSpanMem ℤ i) := by
  simp only [indexEquivOfCartanMatrixEq, Equiv.trans_apply]
  exact Equiv.apply_ofInjective_symm (P₂.rootSpanMem_injective ℤ) _

/-- `RootPairing.Base.indexEquivOfCartanMatrixEq` extends `e` on simple-root indices. -/
@[simp]
theorem indexEquivOfCartanMatrixEq_apply_support [Finite ι₂] [P₂.IsReduced]
    (b : P.Base) (b₂ : P₂.Base) (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) (i : b.support) :
    b.indexEquivOfCartanMatrixEq b₂ e he i = e i := by
  apply P₂.rootSpanMem_injective ℤ
  simp [← toWeightBasisInt_eq_rootSpanMem]

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
