/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Dual.Transpose
public import TauCeti.Algebra.Lie.Multiplicity
-- Non-public: complete reducibility produces the decomposition the count is made over, and a
-- finite-dimensional module is reflexive.
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Lie.Submodule.Decomposition

/-!
# The multiplicity of an irreducible module in a dual module

For Lie modules `M` and `S`, `LieModule.isotypicMultiplicity R L M S` is the finrank of the space
of morphisms `S → M`. This file computes the multiplicity of the dual `S*` in the dual `M*`:

`m_{M*}(S*) = dim (M →ₗ⁅R,L⁆ S)`,

because transposition identifies `S* → M*` with `M → S` once `S` is reflexive
(`TauCeti.LieModule.dualMapEquiv`). The right-hand side counts morphisms *out of* `M`, while the
multiplicity counts morphisms *into* `M`. The two have the same rank when `M` decomposes into
finitely many irreducibles and `S` is irreducible, over any commutative ring. Both spaces split
over the summands; a summand equivalent to `S` contributes a copy of the endomorphisms of `S` to
either space, and by Schur's lemma every other summand contributes nothing. Hence

`m_{M*}(S*) = m_M(S)`

for every finite-dimensional completely reducible `M` and finite-dimensional irreducible `S` over a
field (`LieModule.isotypicMultiplicity_dual_dual`).
Applied to a semisimple Lie algebra, where every finite-dimensional module is completely
reducible, this computes the multiplicities of the dual module from those of the module.

The count of morphisms out of a decomposed module rests on the additivity of the morphism space
over a direct sum in its *source*, `TauCeti.LieModule.directSumLieModuleHomEquiv`, the
counterpart of `TauCeti.LieModule.lieModuleHomDirectSumEquiv` for the target.

## Main results

* `TauCeti.LieModule.directSumLieModuleHomEquiv`: a morphism out of an external direct sum is the
  family of its restrictions to the summands.
* `LieModule.finrank_lieModuleHom_eq_isotypicMultiplicity_of_isInternal`: **for a finite
  decomposition of `M` into irreducibles, the morphisms `M → S` are counted by the multiplicity of
  `S` in `M`.** `LieModule.finrank_lieModuleHom_eq_isotypicMultiplicity` is the same for a
  completely reducible `M`.
* `LieModule.isotypicMultiplicity_dual_dual_eq_finrank`: the multiplicity of `S*` in `M*` is
  `dim (M →ₗ⁅R,L⁆ S)`, for every reflexive `S`.
* `LieModule.isotypicMultiplicity_dual_dual`: **`S*` occurs in `M*` as often as `S` occurs in
  `M`**, for finite-dimensional completely reducible `M` and finite-dimensional irreducible `S`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre I, §3.3.
-/

public section

open Module (Dual finrank)

open scoped DirectSum

universe u v w w₁ w₂

/-! ### Morphisms out of a direct sum -/

namespace TauCeti.LieModule

section Additivity

variable {R : Type u} {L : Type v} {ι : Type w₂} [DecidableEq ι]
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable (R L)
variable (P : ι → Type w₁) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
  [∀ i, LieRingModule L (P i)] [∀ i, _root_.LieModule R L (P i)]
variable (S : Type w) [AddCommGroup S] [Module R S] [LieRingModule L S] [_root_.LieModule R L S]

/-- **The morphism space is additive over a direct sum in its source.** A morphism out of an
external direct sum of Lie modules is the family of its restrictions to the summands, and
conversely a family of morphisms out of the summands assembles to one, by the universal property
`DirectSum.toModule` of the direct sum; this is an isomorphism of `R`-modules. -/
def directSumLieModuleHomEquiv :
    ((⨁ i, P i) →ₗ⁅R,L⁆ S) ≃ₗ[R] Π i, (P i →ₗ⁅R,L⁆ S) where
  toFun f i := f.comp (DirectSum.lieModuleOf R ι L P i)
  map_add' _ _ := by ext i p; simp
  map_smul' _ _ := by ext i p; simp
  invFun g :=
    { toLinearMap := DirectSum.toModule R ι S fun i ↦ (g i : P i →ₗ[R] S)
      map_lie' := fun {x m} ↦ by
        induction m using DirectSum.induction_on with
        | zero => simp
        | of i p =>
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
          rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_lie, DirectSum.toModule_lof,
            DirectSum.toModule_lof]
          exact (g i).map_lie x p
        | add m n hm hn =>
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at hm hn ⊢
          rw [lie_add, map_add, map_add, hm, hn, lie_add] }
  left_inv f := by
    refine LieModuleHom.ext fun x ↦ ?_
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i p => exact DirectSum.toModule_lof R i p
    | add m n hm hn => rw [map_add, hm, hn, map_add]
  right_inv g := by
    exact funext fun j ↦ LieModuleHom.ext fun p ↦
      DirectSum.toModule_lof (φ := fun i ↦ (g i : P i →ₗ[R] S)) R j p

omit [∀ i, _root_.LieModule R L (P i)] in
@[simp]
theorem directSumLieModuleHomEquiv_apply (f : (⨁ i, P i) →ₗ⁅R,L⁆ S) (i : ι) (p : P i) :
    directSumLieModuleHomEquiv R L P S f i p = f (DirectSum.of P i p) :=
  (rfl)

omit [∀ i, _root_.LieModule R L (P i)] in
@[simp]
theorem directSumLieModuleHomEquiv_symm_apply_of (g : Π i, (P i →ₗ⁅R,L⁆ S)) (i : ι) (p : P i) :
    (directSumLieModuleHomEquiv R L P S).symm g (DirectSum.of P i p) = g i p :=
  DirectSum.toModule_lof R i p

end Additivity

end TauCeti.LieModule

namespace LieModule

/-! ### Counting morphisms out of a decomposed module -/

section Count

variable {R : Type u} {L : Type v} {M : Type w} {S : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S] [IsIrreducible R L S]

/-- **The morphisms out of a decomposed module are counted by the multiplicity.** For a finite
decomposition of `M` into irreducible Lie submodules and an irreducible `S`, the morphisms `M → S`
and the morphisms `S → M` span spaces of the same rank. Both spaces split over the summands; a
summand equivalent to `S` contributes a copy of the endomorphisms of `S` to each, and by Schur's
lemma every other summand contributes nothing. -/
theorem finrank_lieModuleHom_eq_isotypicMultiplicity_of_isInternal {ι : Type w₂}
    [DecidableEq ι] [Finite ι] (N : ι → LieSubmodule R L M)
    (h : DirectSum.IsInternal fun i ↦ (N i).toSubmodule) (hirr : ∀ i, IsIrreducible R L (N i)) :
    finrank R (M →ₗ⁅R,L⁆ S) = isotypicMultiplicity R L M S := by
  have _i : Fintype ι := Fintype.ofFinite ι
  -- Summand by summand, the two morphism spaces are isomorphic.
  have hsummand : ∀ i, Nonempty (((N i : Type w) →ₗ⁅R,L⁆ S) ≃ₗ[R] (S →ₗ⁅R,L⁆ N i)) := fun i ↦ by
    have := hirr i
    by_cases hi : Nonempty (S ≃ₗ⁅R,L⁆ N i)
    · exact ⟨(hi.some.congrLeft (P := S)).symm.trans (hi.some.congrRight (M := S))⟩
    · have hempty : IsEmpty (S ≃ₗ⁅R,L⁆ N i) := not_nonempty_iff.mp hi
      have := TauCeti.LieModule.subsingleton_lieModuleHom_of_isEmpty_lieModuleEquiv hempty
      have := TauCeti.LieModule.subsingleton_lieModuleHom_of_isEmpty_lieModuleEquiv
        ⟨fun e : (N i : Type w) ≃ₗ⁅R,L⁆ S ↦ hempty.elim e.symm⟩
      exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  let e := fun i ↦ (hsummand i).some
  -- Assemble them along the decomposition of `M`, in the source and in the target.
  let eM := DirectSum.lieModuleEquivOfIsInternal N h
  rw [isotypicMultiplicity_def, ← (eM.congrLeft (P := S)).finrank_eq,
    ← (eM.congrRight (M := S)).finrank_eq,
    (TauCeti.LieModule.directSumLieModuleHomEquiv R L (fun i ↦ (N i : Type w)) S).finrank_eq,
    (TauCeti.LieModule.lieModuleHomDirectSumEquiv R L S fun i ↦ (N i : Type w)).finrank_eq]
  exact (LinearEquiv.piCongrRight e).finrank_eq

end Count

/-! ### The multiplicity of a dual in a dual -/

section Dual

variable (R : Type u) (L : Type v) (M : Type w) (S : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup S] [Module R S] [LieRingModule L S] [LieModule R L S]

/-- **The multiplicity of `S*` in `M*` counts the morphisms `M → S`**, for reflexive `S`:
transposition identifies `S* → M*` with `M → S`. -/
theorem isotypicMultiplicity_dual_dual_eq_finrank [Module.IsReflexive R S] :
    isotypicMultiplicity R L (Dual R M) (Dual R S) = finrank R (M →ₗ⁅R,L⁆ S) := by
  rw [isotypicMultiplicity_def, (TauCeti.LieModule.dualMapEquiv R L M S).finrank_eq]

end Dual

section CompletelyReducible

variable {K : Type u} {L : Type v} (M : Type w) (S : Type w₁)
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
variable [ComplementedLattice (LieSubmodule K L M)]
variable [AddCommGroup S] [Module K S] [LieRingModule L S] [LieModule K L S] [IsIrreducible K L S]

/-- **For a completely reducible module, the morphisms out of it are counted by the
multiplicity.** A finite-dimensional module whose Lie submodules form a complemented lattice is a
finite direct sum of irreducibles, to which
`LieModule.finrank_lieModuleHom_eq_isotypicMultiplicity_of_isInternal` applies. -/
theorem finrank_lieModuleHom_eq_isotypicMultiplicity :
    finrank K (M →ₗ⁅K,L⁆ S) = isotypicMultiplicity K L M S := by
  obtain ⟨k, N, h, hirr⟩ := TauCeti.exists_isInternal_isIrreducible K L M
  exact finrank_lieModuleHom_eq_isotypicMultiplicity_of_isInternal N h hirr

/-- **`S*` occurs in `M*` as often as `S` occurs in `M`.** Here `M` is a finite-dimensional
completely reducible module and `S` a finite-dimensional irreducible module. The multiplicity of
`S*` in `M*` counts the morphisms `M → S`, and so does the multiplicity of `S` in `M`, by Schur's
lemma on each irreducible summand of `M`. -/
theorem isotypicMultiplicity_dual_dual [FiniteDimensional K S] :
    isotypicMultiplicity K L (Dual K M) (Dual K S) = isotypicMultiplicity K L M S := by
  rw [isotypicMultiplicity_dual_dual_eq_finrank, finrank_lieModuleHom_eq_isotypicMultiplicity]

end CompletelyReducible

end LieModule
