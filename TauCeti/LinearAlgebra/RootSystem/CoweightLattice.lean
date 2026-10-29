/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The coweight lattice of a root datum, and the index of the coroot lattice in it

Let `P` be a root pairing with integer coefficients between a weight lattice `X` and a coweight
lattice `Y`, with finitely many roots. Inside `X` sits the **root lattice** `Q = ℤΦ`, Mathlib's
`RootPairing.rootSpan`, and inside `Y` the **coroot lattice** `Q∨ = ℤΦ∨`, `RootPairing.corootSpan`.
The **coweight lattice** of `P` is the `ℤ`-dual of the root lattice,

`P∨ = Hom_ℤ(Q, ℤ)`,

and the root-coroot pairing restricts to a map `Q∨ → P∨`. This file proves that the map is
injective with **finite** cokernel: the coroot lattice is a finite-index subgroup of the coweight
lattice. The order of `P∨/Q∨` is the quantity classically read off the determinant of the Cartan
matrix, and the quotient is the group that indexes the isogeny forms of a semisimple group with
root system `Φ`.

## The argument

The root lattice is finitely generated, because there are finitely many roots, and it is
torsion-free, because the root-coroot pairing is perfect and therefore makes `X` a reflexive
module. Over the principal ideal domain `ℤ` that makes it free of finite rank
(`TauCeti.free_rootSpan`), so the coweight lattice is free of the same finite rank.

Injectivity of `TauCeti.corootToCoweight` is the nondegeneracy of the canonical bilinear form on
the coweight side. A coroot-lattice element killed by every root is killed by the coroot form
`RootPairing.CorootForm`, whose kernel meets the coroot lattice trivially
(`RootPairing.disjoint_corootSpan_ker_corootForm`); the integers are linearly ordered, so the
anisotropy hypothesis of that theorem is automatic.

Finiteness of the quotient is then a rank count: the coroot lattice and the root lattice have equal
rank (`RootPairing.finrank_corootSpan_eq'`), and a submodule of full rank of a finite free
`ℤ`-module has finite quotient (`Submodule.finiteQuotientOfFreeOfRankEq`).

The quotient is not always trivial -- that is what makes the statement a finiteness theorem rather
than an isomorphism -- but it is trivial in the self-dual situation where the roots span `X` and
the coroots span `Y`, which is Mathlib's `RootPairing.IsRootSystem`
(`TauCeti.corootToCoweight_bijective`). That is the normalization check on the construction: it is
what says the dual was taken on the correct side.

## Main definitions

* `TauCeti.coweightLattice`: the coweight lattice `Hom_ℤ(Q, ℤ)` of a root datum.
* `TauCeti.corootToCoweight`: the coroot lattice inside the coweight lattice, by the root-coroot
  pairing.
* `TauCeti.corootCoweightEquiv`: for a root system, the resulting identification of the coroot
  lattice with the coweight lattice.

## Main results

* `TauCeti.free_rootSpan`, `TauCeti.free_coweightLattice`, `TauCeti.finite_coweightLattice` and
  `TauCeti.finrank_coweightLattice`: the root lattice and the coweight lattice are free `ℤ`-modules
  of the same finite rank.
* `TauCeti.corootToCoweight_injective`: the coroot lattice embeds in the coweight lattice.
* `TauCeti.finite_quotient_range_corootToCoweight`: **the quotient `P∨/Q∨` is finite.**
* `TauCeti.corootToCoweight_surjective` and `TauCeti.corootToCoweight_bijective`: the embedding is
  onto when the roots and the coroots both span, in particular for a root system.
* `TauCeti.finite_quotient_corootSpan` and `TauCeti.finiteIndex_toAddSubgroup_corootSpan`: when the
  roots span the weight lattice, the coweight lattice is `Y` itself, and the coroot lattice has
  finite index in `Y`.

The statements for the **weight** lattice `Hom_ℤ(Q∨, ℤ)` and the root lattice inside it are these
statements for `RootPairing.flip`, which exchanges roots and coroots; they are not restated.

## Implementation notes

The integers are the natural level of generality here, not a restriction: a root pairing whose
weight and coweight spaces are honest lattices is exactly a `RootPairing.RootDatum`, which is
`RootPairing ι ℤ X Y`. Over a general principal ideal domain the same rank count shows only that
the quotient is torsion; finiteness is special to `ℤ`, and over a field the two spans are already
dual to one another, so there is nothing to measure.

Mathlib supplies the *individual* functionals that a root or a coroot defines on the opposite span,
`RootPairing.root'In` and `RootPairing.coroot'In`, but no map out of the whole lattice;
`TauCeti.corootToCoweight` is that bundled map, and `TauCeti.corootToCoweight_apply_rootSpanMem`
evaluates it at a root.

## References

* [N. Bourbaki, *Lie groups and Lie algebras. Chapters 4--6*][bourbaki1968], Chapter VI, § 1, no. 9.
* M. Demazure, *SGA III, Exposé XXI, Données Radicielles*, 6.2.
-/

public section

namespace TauCeti

open Module

universe u v w

variable {ι : Type u} {X : Type v} {Y : Type w}
  [AddCommGroup X] [AddCommGroup Y] (P : RootPairing ι ℤ X Y)

/-- The **coweight lattice** of a root datum: the `ℤ`-dual `Hom_ℤ(Q, ℤ)` of its root lattice
`Q = ℤΦ`. The root-coroot pairing embeds the coroot lattice in it with finite index
(`TauCeti.finite_quotient_range_corootToCoweight`), so it is a lattice of the same rank. -/
abbrev coweightLattice := Module.Dual ℤ (P.rootSpan ℤ)

/-- The **coroot lattice inside the coweight lattice**: a coroot-lattice element is read as the
integer-valued functional it defines on the root lattice. -/
def corootToCoweight : P.corootSpan ℤ →ₗ[ℤ] coweightLattice P :=
  (P.rootSpan ℤ).subtype.dualMap ∘ₗ P.toLinearMap.flip ∘ₗ (P.corootSpan ℤ).subtype

@[simp]
theorem corootToCoweight_apply_apply (y : P.corootSpan ℤ) (x : P.rootSpan ℤ) :
    corootToCoweight P y x = P.toLinearMap x y :=
  (rfl)

theorem corootToCoweight_apply_rootSpanMem (y : P.corootSpan ℤ) (i : ι) :
    corootToCoweight P y (P.rootSpanMem ℤ i) = P.root' i (y : Y) :=
  (rfl)

/-! ### The root lattice and the coweight lattice are finite free -/

/-- The root lattice of a root datum over `ℤ` is torsion-free: it sits inside the weight lattice,
which the perfect root-coroot pairing makes reflexive. -/
theorem isTorsionFree_rootSpan : Module.IsTorsionFree ℤ (P.rootSpan ℤ) :=
  have : Module.IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  (Submodule.injective_subtype _).moduleIsTorsionFree _ fun _ _ ↦ rfl

/-- **The root lattice of a root datum over `ℤ` is free of finite rank.** It is finitely generated
because there are finitely many roots, and torsion-free because the root-coroot pairing is
perfect. -/
theorem free_rootSpan [Finite ι] : Module.Free ℤ (P.rootSpan ℤ) :=
  have := isTorsionFree_rootSpan P
  inferInstance

/-- The coweight lattice is a free `ℤ`-module, being the dual of a finite free one. -/
theorem free_coweightLattice [Finite ι] : Module.Free ℤ (coweightLattice P) :=
  have := free_rootSpan P
  inferInstance

/-- The coweight lattice is a finitely generated `ℤ`-module. -/
theorem finite_coweightLattice [Finite ι] : Module.Finite ℤ (coweightLattice P) :=
  have := free_rootSpan P
  inferInstance

/-- The coweight lattice has the rank of the root lattice. -/
theorem finrank_coweightLattice [Finite ι] :
    finrank ℤ (coweightLattice P) = finrank ℤ (P.rootSpan ℤ) :=
  have := free_rootSpan P
  Module.finrank_linearMap_self ℤ ℤ _

/-! ### The coroot lattice is a finite-index sublattice -/

/-- **The coroot lattice embeds in the coweight lattice.** A coroot-lattice element on which every
root vanishes is isotropic for the coroot form, whose kernel meets the coroot lattice trivially. -/
theorem corootToCoweight_injective [Finite ι] :
    Function.Injective (corootToCoweight P) := by
  have := Fintype.ofFinite ι
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).2 fun y hy ↦ ?_
  rw [LinearMap.mem_ker] at hy
  have hroot (i : ι) : P.root' i (y : Y) = 0 := by
    rw [← corootToCoweight_apply_rootSpanMem P y i, hy, LinearMap.zero_apply]
  have hker : (y : Y) ∈ LinearMap.ker P.CorootForm :=
    LinearMap.mem_ker.2 <| LinearMap.ext fun z ↦ by
      simp [P.corootForm_apply_apply, hroot]
  exact Subtype.ext <|
    Submodule.disjoint_def.mp P.disjoint_corootSpan_ker_corootForm _ y.2 hker

/-- The image of the coroot lattice has the full rank of the coweight lattice. -/
theorem finrank_range_corootToCoweight [Finite ι] :
    finrank ℤ (LinearMap.range (corootToCoweight P)) = finrank ℤ (coweightLattice P) := by
  have := Fintype.ofFinite ι
  rw [LinearMap.finrank_range_of_inj (corootToCoweight_injective P), finrank_coweightLattice,
    P.finrank_corootSpan_eq']

/-- **The coroot lattice has finite index in the coweight lattice**: the quotient `P∨/Q∨` of a
root datum with finitely many roots is a finite group. -/
theorem finite_quotient_range_corootToCoweight [Finite ι] :
    Finite (coweightLattice P ⧸ LinearMap.range (corootToCoweight P)) :=
  have := free_coweightLattice P
  have := finite_coweightLattice P
  Submodule.finiteQuotientOfFreeOfRankEq _ (finrank_range_corootToCoweight P)

/-! ### Spanning roots and coroots

When the roots span the weight lattice `X`, the perfect pairing identifies `Y` with the coweight
lattice `Hom_ℤ(X, ℤ) = Hom_ℤ(Q, ℤ)`, and the results above become results about the coroot lattice
inside `Y` itself. If moreover the coroots span `Y` -- the case of `RootPairing.IsRootSystem` --
the two lattices coincide and the quotient is trivial. -/

section Spanning

/-- If the roots span the weight lattice, then the weight lattice is free of finite rank. -/
theorem free_of_rootSpan_eq_top [Finite ι] (hP : P.rootSpan ℤ = ⊤) : Module.Free ℤ X :=
  have := free_rootSpan P
  Module.Free.of_equiv (LinearEquiv.ofTop _ hP)

/-- If the roots span the weight lattice, then the weight lattice is finitely generated. -/
theorem finite_of_rootSpan_eq_top [Finite ι] (hP : P.rootSpan ℤ = ⊤) : Module.Finite ℤ X :=
  Module.Finite.equiv (LinearEquiv.ofTop _ hP)

/-- If the roots span the weight lattice, then the coweight lattice is free of finite rank: the
perfect pairing identifies it with the `ℤ`-dual of the weight lattice. -/
theorem free_coweight_of_rootSpan_eq_top [Finite ι] (hP : P.rootSpan ℤ = ⊤) : Module.Free ℤ Y :=
  have := free_of_rootSpan_eq_top P hP
  have := finite_of_rootSpan_eq_top P hP
  Module.Free.of_equiv P.toLinearMap.flip.toPerfPair.symm

/-- If the roots span the weight lattice, then the coweight lattice is finitely generated. -/
theorem finite_coweight_of_rootSpan_eq_top [Finite ι] (hP : P.rootSpan ℤ = ⊤) :
    Module.Finite ℤ Y :=
  have := free_of_rootSpan_eq_top P hP
  have := finite_of_rootSpan_eq_top P hP
  Module.Finite.equiv P.toLinearMap.flip.toPerfPair.symm

/-- If the roots span the weight lattice, then the two lattices of a root datum have equal rank. -/
theorem finrank_eq_finrank_of_rootSpan_eq_top [Finite ι] (hP : P.rootSpan ℤ = ⊤) :
    finrank ℤ Y = finrank ℤ X :=
  have := free_of_rootSpan_eq_top P hP
  have := finite_of_rootSpan_eq_top P hP
  (Module.finrank_of_isPerfPair P.toLinearMap).symm

/-- **The coroot lattice has finite index in the coweight lattice of a root datum whose roots span
the weight lattice.** This is `TauCeti.finite_quotient_range_corootToCoweight` read on `Y`, which
the perfect pairing identifies with `Hom_ℤ(Q, ℤ)`. -/
theorem finite_quotient_corootSpan [Finite ι] (hP : P.rootSpan ℤ = ⊤) :
    Finite (Y ⧸ P.corootSpan ℤ) :=
  have := Fintype.ofFinite ι
  have := free_coweight_of_rootSpan_eq_top P hP
  have := finite_coweight_of_rootSpan_eq_top P hP
  Submodule.finiteQuotientOfFreeOfRankEq _ <| by
    rw [P.finrank_corootSpan_eq', finrank_eq_finrank_of_rootSpan_eq_top P hP,
      (LinearEquiv.ofTop (P.rootSpan ℤ) hP).finrank_eq]

/-- The index form of `TauCeti.finite_quotient_corootSpan`. -/
theorem finiteIndex_toAddSubgroup_corootSpan [Finite ι] (hP : P.rootSpan ℤ = ⊤) :
    (P.corootSpan ℤ).toAddSubgroup.FiniteIndex :=
  have : Finite (Y ⧸ (P.corootSpan ℤ).toAddSubgroup) := finite_quotient_corootSpan P hP
  AddSubgroup.finiteIndex_of_finite_quotient

/-- **The embedding of the coroot lattice in the coweight lattice is onto when both the roots and
the coroots span.** Together with injectivity this says that a root datum which is at once adjoint
(the roots span the weight lattice) and simply connected (the coroots span the coweight lattice)
has trivial `P∨/Q∨`. -/
theorem corootToCoweight_surjective (hP : P.rootSpan ℤ = ⊤) (hQ : P.corootSpan ℤ = ⊤) :
    Function.Surjective (corootToCoweight P) := by
  intro f
  refine ⟨⟨P.toLinearMap.flip.toPerfPair.symm
    (f ∘ₗ (LinearEquiv.ofTop (P.rootSpan ℤ) hP).symm.toLinearMap),
      hQ.ge Submodule.mem_top⟩, ?_⟩
  ext x
  have hx : (LinearEquiv.ofTop (P.rootSpan ℤ) hP).symm (x : X) = x :=
    Subtype.ext (LinearEquiv.coe_ofTop_symm_apply _ _)
  rw [corootToCoweight_apply_apply, LinearMap.apply_toPerfPair_flip, LinearMap.comp_apply,
    LinearEquiv.coe_coe, hx]

/-- The coroot lattice of a root *system* over `ℤ` is its coweight lattice. -/
theorem corootToCoweight_bijective [Finite ι] [P.IsRootSystem] :
    Function.Bijective (corootToCoweight P) :=
  ⟨corootToCoweight_injective P,
    corootToCoweight_surjective P RootPairing.IsRootSystem.span_root_eq_top
      RootPairing.IsRootSystem.span_coroot_eq_top⟩

/-- The coroot lattice of a root system over `ℤ`, identified with its coweight lattice. -/
noncomputable def corootCoweightEquiv [Finite ι] [P.IsRootSystem] :
    P.corootSpan ℤ ≃ₗ[ℤ] coweightLattice P :=
  LinearEquiv.ofBijective _ (corootToCoweight_bijective P)

@[simp]
theorem corootCoweightEquiv_apply [Finite ι] [P.IsRootSystem] (y : P.corootSpan ℤ) :
    corootCoweightEquiv P y = corootToCoweight P y :=
  (rfl)

end Spanning

end TauCeti
