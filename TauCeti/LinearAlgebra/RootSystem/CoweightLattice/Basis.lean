/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.CoweightLattice

/-!
# The fundamental coweights and the index of the coroot lattice

Let `b` be a base of a root system `P` with weight space `M` and coweight space `N`. The simple
roots form a basis of `M` (`RootPairing.Base.toWeightBasis`), so the perfect pairing identifies `N`
with the dual of `M`, and the dual basis is the basis of **fundamental coweights** `ϖᵢ` of `N`,
characterized by `⟨αᵢ, ϖⱼ⟩ = δᵢⱼ`. The coordinate of a coweight `x` at `ϖᵢ` is `⟨αᵢ, x⟩`.

Every root is, up to sign, a natural combination of the simple roots, so a coweight lies in the
coweight lattice `P∨ = RootPairing.coweightLattice` (the coweights at which every root is an
integer) as soon as the simple roots are integers at it. Hence, over a coefficient ring of
characteristic zero, the fundamental coweights form a `ℤ`-basis of `P∨`.

The simple coroots form a `ℤ`-basis of the coroot lattice `Q∨`, and the coordinates of `αⱼ^∨` in
the fundamental coweights are the Cartan integers `⟨αᵢ, αⱼ^∨⟩`. So the matrix of the inclusion
`Q∨ ⊆ P∨` in these bases is the Cartan matrix, and the index of `Q∨` in `P∨` is the absolute value
of its determinant. For an irreducible root system the finite group `P∨ / Q∨` is the stabilizer of
the fundamental alcove in the extended affine Weyl group and the centre of the simply connected
compact group; the determinant computes its order, for instance `r + 1` in type `A_r`, `4` in type
`D₄` and `3` in type `E₆`.

## Main definitions

* `RootPairing.Base.fundamentalCoweightBasis`: the basis of the coweight space dual to the simple
  roots.
* `RootPairing.Base.coweightLatticeBasis`: the fundamental coweights as a `ℤ`-basis of the coweight
  lattice.

## Main results

* `RootPairing.Base.fundamentalCoweightBasis_repr`: the coordinates of a coweight are its pairings
  with the simple roots.
* `RootPairing.Base.mem_coweightLattice_iff`: integrality on the simple roots suffices for
  membership in the coweight lattice.
* `RootPairing.Base.relIndex_corootSpan_coweightLattice`: **the index of the coroot lattice in the
  coweight lattice is the absolute value of the determinant of the Cartan matrix.**

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI, §1.10 and Plates I–IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.1.
-/

public section

open Module Submodule

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [P.IsRootSystem] (b : P.Base)

/-- **The fundamental coweights** of a base `b` of a root system: the basis `ϖᵢ` of the coweight
space dual to the basis of simple roots, so that `⟨αᵢ, ϖⱼ⟩ = δᵢⱼ`
(`RootPairing.Base.root'_fundamentalCoweightBasis`). -/
noncomputable def fundamentalCoweightBasis : Basis b.support R N := by
  classical
  exact b.toWeightBasis.dualBasis.map P.flip.toPerfPair.symm

/-- **The coordinates of a coweight in the fundamental coweights** are its pairings with the
simple roots. -/
@[simp]
theorem fundamentalCoweightBasis_repr (x : N) (i : b.support) :
    b.fundamentalCoweightBasis.repr x i = P.root' i x := by
  classical
  simp [fundamentalCoweightBasis]

/-- The simple roots pair with the fundamental coweights by the Kronecker delta,
`⟨αᵢ, ϖⱼ⟩ = δᵢⱼ`. -/
@[simp]
theorem root'_fundamentalCoweightBasis [DecidableEq ι] (i j : b.support) :
    P.root' i (b.fundamentalCoweightBasis j) = if i = j then 1 else 0 := by
  rw [← fundamentalCoweightBasis_repr, Basis.repr_self, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

omit [P.IsRootSystem] in
/-- **A coweight lies in the coweight lattice iff every simple root takes an integer value at
it.** -/
theorem mem_coweightLattice_iff {x : N} :
    x ∈ P.coweightLattice ↔ ∀ i : b.support, ∃ z : ℤ, P.root' i x = z := by
  refine ⟨fun hx i ↦ P.mem_coweightLattice.1 hx i, fun hx ↦ P.mem_coweightLattice.2 fun k ↦ ?_⟩
  choose z hz using hx
  obtain ⟨f, -, hf | hf⟩ := b.exists_root_eq_sum_nat_or_neg k
  · refine ⟨∑ j : b.support, (f j : ℤ) * z j, ?_⟩
    rw [root', hf, ← Finset.sum_coe_sort b.support]
    simp [hz]
  · refine ⟨-∑ j : b.support, (f j : ℤ) * z j, ?_⟩
    rw [root', hf, ← Finset.sum_coe_sort b.support]
    simp [hz]

/-- The fundamental coweights lie in the coweight lattice. -/
theorem fundamentalCoweightBasis_mem_coweightLattice (i : b.support) :
    b.fundamentalCoweightBasis i ∈ P.coweightLattice := by
  classical
  refine b.mem_coweightLattice_iff.2 fun j ↦ ⟨if j = i then 1 else 0, ?_⟩
  rw [root'_fundamentalCoweightBasis]
  split_ifs <;> simp

variable [CharZero R]

/-- **The fundamental coweights form a `ℤ`-basis of the coweight lattice.** -/
noncomputable def coweightLatticeBasis : Basis b.support ℤ P.coweightLattice :=
  Basis.mk
    (v := fun i ↦ ⟨b.fundamentalCoweightBasis i, b.fundamentalCoweightBasis_mem_coweightLattice i⟩)
    (LinearIndependent.of_comp P.coweightLattice.subtype
      (b.fundamentalCoweightBasis.linearIndependent.restrict_scalars' ℤ))
    (fun x _ ↦ by
      classical
      choose z hz using b.mem_coweightLattice_iff.1 x.2
      refine (mem_span_range_iff_exists_fun ℤ).2 ⟨z, Subtype.ext ?_⟩
      refine b.fundamentalCoweightBasis.ext_elem fun i ↦ ?_
      simp [hz, Finsupp.single_apply])

/-- The `ℤ`-basis of the coweight lattice consists of the fundamental coweights. -/
@[simp]
theorem coe_coweightLatticeBasis (i : b.support) :
    (b.coweightLatticeBasis i : N) = b.fundamentalCoweightBasis i := by
  simp [coweightLatticeBasis]

/-- The coordinates of a point of the coweight lattice in its `ℤ`-basis of fundamental coweights
are its pairings with the simple roots. -/
@[simp]
theorem coweightLatticeBasis_repr (x : P.coweightLattice) (i : b.support) :
    (b.coweightLatticeBasis.repr x i : R) = P.root' i x := by
  rw [← fundamentalCoweightBasis_repr]
  conv_rhs => rw [← b.coweightLatticeBasis.sum_repr x]
  classical
  simp [Finsupp.single_apply]

/-- **The index of the coroot lattice in the coweight lattice is the absolute value of the
determinant of the Cartan matrix**, `[P∨ : Q∨] = |det C|`, for a crystallographic root system
over a ring of characteristic zero. -/
theorem relIndex_corootSpan_coweightLattice [DecidableEq ι] [P.IsCrystallographic] :
    (P.corootSpan ℤ).toAddSubgroup.relIndex P.coweightLattice.toAddSubgroup =
      b.cartanMatrix.det.natAbs := by
  -- `Base.flip` keeps the support, but only up to unfolding, so the coroot basis is restated over
  -- `b.support`; both bases are moved to the `toIntSubmodule` form used by the index formula.
  let bQ : Basis b.support ℤ (P.corootSpan ℤ).toAddSubgroup.toIntSubmodule :=
    b.flip.toWeightBasisInt.map
      (LinearEquiv.ofEq _ _ (Submodule.toAddSubgroup_toIntSubmodule _).symm)
  let bP : Basis b.support ℤ P.coweightLattice.toAddSubgroup.toIntSubmodule :=
    b.coweightLatticeBasis.map
      (LinearEquiv.ofEq _ _ (Submodule.toAddSubgroup_toIntSubmodule _).symm)
  have hP (y) (i) : (bP.repr y i : R) = P.root' i y := by
    simp only [bP, Basis.map_repr, LinearEquiv.trans_apply]
    exact b.coweightLatticeBasis_repr _ i
  have hQ (j) : (bQ j : N) = P.coroot j := b.flip.coe_toWeightBasisInt_apply j
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ P.corootSpan_le_coweightLattice bQ bP,
    Basis.det_apply]
  congr 2
  ext i j
  rw [Basis.toMatrix_apply, ← Int.cast_inj (α := R), hP, hQ]
  simp [cartanMatrix, cartanMatrixIn_def, ← P.algebraMap_pairingIn ℤ]

end RootPairing.Base
