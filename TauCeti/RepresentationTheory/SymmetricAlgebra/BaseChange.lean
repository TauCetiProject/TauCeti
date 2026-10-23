/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Reynolds

/-!
# Scalar extension of symmetric-algebra invariants

The canonical comparison `S ⊗[R] Sym(M) ≃ Sym(S ⊗[R] M)` is equivariant for the
representations induced by a linear action on `M`. For a finite group and a flat scalar
extension, it restricts to an algebra equivalence
`S ⊗[R] Sym(M)^G ≃ Sym(S ⊗[R] M)^G`. Its inclusion into the ambient symmetric algebra is
the scalar extension of the original inclusion, followed by the canonical comparison.
Thus it preserves homogeneous degree. When the group order is invertible, the comparison
also intertwines the Reynolds projections.

Applied to the contragredient representation on `V*`, this identifies polynomial invariants
after extension of the coefficient field. Flatness suffices for the invariant-algebra
comparison in every characteristic; invertibility of the group order is needed only for
the Reynolds operators. No finite generation or freeness assumption on `M` is required.

The invariant-module comparison is `Representation.invariantsBaseChangeEquiv`; the
ambient graded comparison is `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`.

## Main declarations

* `Representation.symmetricAlgebraBaseChangeEquiv`: equivariance of the ambient comparison.
* `Representation.symmetricAlgebraInvariantsBaseChangeEquiv`: flat scalar extension of
  finite-group invariant algebras.
* `Representation.symmetricAlgebraReynolds_baseChange`: compatibility of Reynolds projection
  with this algebra equivalence.
-/

public section

open TensorProduct
open TauCeti.SymmetricAlgebra

namespace Representation

variable {R S G M : Type*}

section Semiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S] [Monoid G]
  [AddCommMonoid M] [Module R M] (ρ : Representation R G M)

/-- The canonical scalar-extension comparison for symmetric algebras is equivariant. -/
noncomputable def symmetricAlgebraBaseChangeEquiv :
    (ρ.symmetricAlgebra.baseChange S).Equiv (ρ.baseChange S).symmetricAlgebra :=
  .mk (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toLinearEquiv fun g ↦ by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s p
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgEquiv.coe_toLinearEquiv,
      AlgEquiv.coe_toAlgHom, BialgEquiv.coe_toAlgEquiv, baseChange_apply,
      LinearMap.baseChange_tmul,
      symmetricAlgebra_apply, AlgHom.toLinearMap_apply, AlgHom.coe_comp,
      Function.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] using
      DFunLike.congr_fun (LinearMap.scalarTensorBialgEquiv_comp_map (S := S) (ρ g))
        (s ⊗ₜ[R] p)

/-- The equivariant comparison has the usual symmetric-algebra comparison as its function. -/
@[simp]
theorem symmetricAlgebraBaseChangeEquiv_apply (z : S ⊗[R] SymmetricAlgebra R M) :
    ρ.symmetricAlgebraBaseChangeEquiv z = scalarTensorBialgEquiv (k := R) (K := S) z :=
  (rfl)

end Semiring

section Flat

variable [CommRing R] [CommRing S] [Algebra R S] [Group G] [Finite G]
  [AddCommMonoid M] [Module R M] [Module.Flat R S] (ρ : Representation R G M)

private noncomputable def invariantsBaseChangeLinearEquiv :
    S ⊗[R] ρ.symmetricAlgebraInvariants ≃ₗ[S]
      (ρ.baseChange S).symmetricAlgebraInvariants :=
  (AlgebraTensorModule.congr (LinearEquiv.refl S S)
      (ρ.symmetricAlgebraInvariants.toSubmoduleEquiv.symm.trans
        (LinearEquiv.ofEq _ _ ρ.toSubmodule_symmetricAlgebraInvariants))).trans <|
    (ρ.symmetricAlgebra.invariantsBaseChangeEquiv (A := S)).trans <|
      (ρ.symmetricAlgebraBaseChangeEquiv.invariantsLinearEquiv).trans
        ((LinearEquiv.ofEq _ _ (ρ.baseChange S).toSubmodule_symmetricAlgebraInvariants.symm).trans
          (ρ.baseChange S).symmetricAlgebraInvariants.toSubmoduleEquiv)

private theorem coe_invariantsBaseChangeLinearEquiv
    (z : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    (ρ.invariantsBaseChangeLinearEquiv z : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        ((Algebra.TensorProduct.map (AlgHom.id S S) ρ.symmetricAlgebraInvariants.val) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s p =>
    simp only [invariantsBaseChangeLinearEquiv, LinearEquiv.trans_apply,
      AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.val_apply]
    -- The outer inclusion is a subalgebra coercion, whereas `coe_ofEq_apply` is stated
    -- for submodule coercions. `erw` recognizes their common underlying subtype map.
    erw [LinearEquiv.coe_ofEq_apply, Equiv.coe_invariantsLinearEquiv_apply,
      symmetricAlgebraBaseChangeEquiv_apply, coe_invariantsBaseChangeEquiv,
      LinearMap.lTensor_tmul, Submodule.subtype_apply, LinearEquiv.coe_ofEq_apply]
  | add x y hx hy => simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) hx hy

/-- Flat scalar extension commutes with the invariant subalgebra of a finite group acting
on a symmetric algebra. This is an algebra equivalence, including in modular characteristic. -/
noncomputable def symmetricAlgebraInvariantsBaseChangeEquiv :
    S ⊗[R] ρ.symmetricAlgebraInvariants ≃ₐ[S]
      (ρ.baseChange S).symmetricAlgebraInvariants :=
  AlgEquiv.ofLinearEquiv ρ.invariantsBaseChangeLinearEquiv
    (Subtype.ext <| by rw [coe_invariantsBaseChangeLinearEquiv]; simp)
    (fun x y ↦ Subtype.ext <| by simp only [coe_invariantsBaseChangeLinearEquiv, map_mul,
      Subalgebra.coe_mul])

/-- The invariant-algebra comparison is induced by the scalar-extended inclusion into the
ambient symmetric algebra. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsBaseChangeEquiv
    (z : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    (ρ.symmetricAlgebraInvariantsBaseChangeEquiv z : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        ((Algebra.TensorProduct.map (AlgHom.id S S) ρ.symmetricAlgebraInvariants.val) z) :=
  ρ.coe_invariantsBaseChangeLinearEquiv z

/-- The inverse comparison agrees with the inverse ambient comparison after inclusion. -/
@[simp]
theorem map_symmetricAlgebraInvariantsBaseChangeEquiv_symm
    (p : (ρ.baseChange S).symmetricAlgebraInvariants) :
    (Algebra.TensorProduct.map (AlgHom.id S S) ρ.symmetricAlgebraInvariants.val)
        (ρ.symmetricAlgebraInvariantsBaseChangeEquiv.symm p) =
      (scalarTensorBialgEquiv (k := R) (K := S)).symm
        (p : SymmetricAlgebra S (S ⊗[R] M)) := by
  apply (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.injective
  simp only [BialgEquiv.coe_toAlgEquiv]
  rw [← coe_symmetricAlgebraInvariantsBaseChangeEquiv, AlgEquiv.apply_symm_apply,
    BialgEquiv.apply_symm_apply]

end Flat

section Reynolds

variable [CommRing R] [CommRing S] [Algebra R S] [Group G] [Fintype G]
  [AddCommMonoid M] [Module R M] [Module.Flat R S]
  [Invertible (Fintype.card G : R)] [Invertible (Fintype.card G : S)]
  (ρ : Representation R G M)

/-- Reynolds projection commutes with flat scalar extension under the canonical
invariant-algebra comparison. -/
theorem symmetricAlgebraReynolds_baseChange (z : S ⊗[R] SymmetricAlgebra R M) :
    (ρ.baseChange S).symmetricAlgebraReynolds
        (scalarTensorBialgEquiv (k := R) (K := S) z) =
      ρ.symmetricAlgebraInvariantsBaseChangeEquiv
        ((ρ.symmetricAlgebraReynolds.restrictScalars R).baseChange S z) := by
  apply Subtype.ext
  rw [coe_symmetricAlgebraInvariantsBaseChangeEquiv]
  induction z using TensorProduct.inductionOn with
  | tmul s p =>
    have hinv : algebraMap R S (⅟(Fintype.card G : R)) = ⅟(Fintype.card G : S) := by
      let : Invertible (algebraMap R S (Fintype.card G : R)) :=
        (show algebraMap R S (Fintype.card G : R) = (Fintype.card G : S) from
          map_natCast _ _) ▸ inferInstance
      simpa only [map_natCast] using map_invOf (algebraMap R S) (Fintype.card G : R)
    have hequiv (g : G) (x : S ⊗[R] SymmetricAlgebra R M) :
        (ρ.baseChange S).symmetricAlgebra g
            (scalarTensorBialgEquiv (k := R) (K := S) x) =
          scalarTensorBialgEquiv (k := R) (K := S)
            ((ρ.symmetricAlgebra g).baseChange S x) := by
      simpa only [Equiv.coe_toIntertwiningMap, symmetricAlgebraBaseChangeEquiv_apply,
        baseChange_apply] using (IntertwiningMap.isIntertwining _ _
          ρ.symmetricAlgebraBaseChangeEquiv.toIntertwiningMap g x).symm
    simp only [coe_symmetricAlgebraReynolds_eq_sum, hequiv,
      LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.val_apply]
    rw [tmul_smul, tmul_sum, ← algebraMap_smul S (⅟(Fintype.card G : R)), hinv,
      map_smul, map_sum]
  | add x y hx hy =>
    simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (· + ·) hx hy

end Reynolds

end Representation
