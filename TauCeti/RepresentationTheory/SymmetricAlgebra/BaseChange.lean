/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Reynolds

/-!
# Scalar extension of polynomial invariants

Let `ρ` be a representation of a group `G` on an `R`-module `M`, and let `S` be a commutative
`R`-algebra. The canonical equivalence `S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`
(`TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`) is equivariant: it intertwines the scalar
extension of the induced action of `G` on `Sym M` with the action induced by the scalar-extended
representation `ρ.baseChange S`. This file draws the consequences for invariants.

* For a finite group and a flat `R`-algebra `S`, the invariant subalgebra commutes with scalar
  extension: `S ⊗[R] Sym(M)^G ≃ Sym(S ⊗[R] M)^G` as `S`-algebras. This is the flat base change
  of finite-group invariants (`Representation.invariantsBaseChangeEquiv`), transported along the
  equivariant equivalence; the comparison map is the scalar extension of the inclusion of the
  invariants, so it is an algebra map.
* When `#G` is invertible, the Reynolds operator commutes with scalar extension, with no flatness
  hypothesis: averaging over `G` is a finite sum, so it commutes with `S ⊗[R] -`
  (`Representation.averageMap_baseChange`).
* Over a field `K`, the dimension of each homogeneous component of the invariant subalgebra does
  not change under extension to any nontrivial commutative `K`-algebra. Thus the Hilbert series of
  `Sym(M)^G` is unchanged by extending scalars, for instance from `ℚ` to `ℝ` or from `ℝ` to `ℂ`.

## Main declarations

* `Representation.symmetricAlgebraBaseChangeEquiv`: the scalar extension of the induced
  representation on `Sym M` is equivalent to the representation induced by `ρ.baseChange S`.
* `Representation.symmetricAlgebraInvariantsBaseChangeEquiv`: flat scalar extension of the invariant
  subalgebra, as an algebra equivalence.
* `Representation.coe_symmetricAlgebraReynolds_scalarTensorBialgEquiv_tmul`: the Reynolds operator
  commutes with scalar extension.
* `Representation.finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule`: the
  graded dimensions of the invariant subalgebra are invariant under scalar extension of fields.

## References

* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 2.
-/

public section

open TensorProduct TauCeti.SymmetricAlgebra

namespace Representation

variable {R S G M : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S] [Monoid G] [AddCommMonoid M]
  [Module R M]
variable (ρ : Representation R G M)

/-- The scalar extension of the representation induced by `ρ` on `Sym M` is equivalent to the
representation induced by the scalar-extended representation `ρ.baseChange S` on
`Sym (S ⊗[R] M)`. The underlying linear equivalence is the canonical equivalence
`S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`. -/
noncomputable def symmetricAlgebraBaseChangeEquiv (S : Type*) [CommSemiring S] [Algebra R S] :
    (ρ.symmetricAlgebra.baseChange S).Equiv (ρ.baseChange S).symmetricAlgebra :=
  .mk (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toLinearEquiv fun g ↦ by
    refine TensorProduct.AlgebraTensorModule.ext fun s p ↦ ?_
    have h := congr($(LinearMap.scalarTensorBialgEquiv_comp_map (S := S) (ρ g)) (s ⊗ₜ[R] p))
    simpa using h

/-- The equivalence `Representation.symmetricAlgebraBaseChangeEquiv` is the canonical
scalar-extension equivalence of symmetric algebras. -/
@[simp]
theorem symmetricAlgebraBaseChangeEquiv_apply (x : S ⊗[R] SymmetricAlgebra R M) :
    ρ.symmetricAlgebraBaseChangeEquiv S x = scalarTensorBialgEquiv (k := R) (K := S) x :=
  (rfl)

/-- The inverse of `Representation.symmetricAlgebraBaseChangeEquiv` is the inverse of the
canonical scalar-extension equivalence of symmetric algebras. -/
@[simp]
theorem symmetricAlgebraBaseChangeEquiv_symm_apply (y : SymmetricAlgebra S (S ⊗[R] M)) :
    (ρ.symmetricAlgebraBaseChangeEquiv S).symm y =
      (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).symm y :=
  (rfl)

/-- The scalar extension of an invariant is invariant: the canonical algebra map
`S ⊗[R] Sym(M)^G → Sym (S ⊗[R] M)` lands in the invariant subalgebra of `ρ.baseChange S`. -/
theorem scalarTensorBialgEquiv_lTensor_val_mem_symmetricAlgebraInvariants
    (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    scalarTensorBialgEquiv (k := R) (K := S)
        (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x) ∈
      (ρ.baseChange S).symmetricAlgebraInvariants := by
  refine ((ρ.baseChange S).mem_symmetricAlgebraInvariants _).2 fun g ↦ ?_
  have h := IntertwiningMap.isIntertwining _ _
    (ρ.symmetricAlgebraBaseChangeEquiv S).toIntertwiningMap g
    (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x)
  simp only [Equiv.coe_toIntertwiningMap, symmetricAlgebraBaseChangeEquiv_apply] at h
  rw [← h]
  congr 1
  clear h
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
      simp [(ρ.mem_symmetricAlgebraInvariants a).1 a.2 g]

end CommSemiring

section Invariants

variable [CommRing R] [CommRing S] [Algebra R S] [Group G] [AddCommGroup M] [Module R M]
variable (ρ : Representation R G M)

variable [Module.Flat R S] [Finite G]

/-- Every invariant of `ρ.baseChange S` is the image of the scalar extension of an invariant of
`ρ`, when `S` is flat over `R`. -/
private theorem exists_scalarTensorBialgEquiv_lTensor_val_eq
    {y : SymmetricAlgebra S (S ⊗[R] M)} (hy : y ∈ (ρ.baseChange S).symmetricAlgebraInvariants) :
    ∃ x : S ⊗[R] ρ.symmetricAlgebraInvariants, scalarTensorBialgEquiv (k := R) (K := S)
      (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x) = y := by
  -- Pull `y` back to an invariant of the scalar extension of the induced representation, which
  -- is the scalar extension of an invariant by flatness.
  let e := ρ.symmetricAlgebraBaseChangeEquiv S
  have hy' : e.symm y ∈ (ρ.symmetricAlgebra.baseChange S).invariants := by
    have := (e.symm.invariantsLinearEquiv ⟨y, (mem_invariants _ y).2
      (((ρ.baseChange S).mem_symmetricAlgebraInvariants y).1 hy)⟩).2
    rwa [Equiv.coe_invariantsLinearEquiv_apply] at this
  -- The invariant submodule of the induced representation is the invariant subalgebra.
  let r : ρ.symmetricAlgebra.invariants →ₗ[R] ρ.symmetricAlgebraInvariants :=
    ρ.symmetricAlgebraInvariants.toSubmoduleEquiv.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ ρ.toSubmodule_symmetricAlgebraInvariants.symm).toLinearMap
  have hr (z : S ⊗[R] ρ.symmetricAlgebra.invariants) :
      Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val
        (r.lTensor S z) = ρ.symmetricAlgebra.invariants.subtype.lTensor S z := by
    induction z with
    | add x y hx hy => simp only [map_add, hx, hy]
    -- `Subalgebra.toSubmoduleEquiv` and `LinearEquiv.ofEq` do not change the underlying element,
    -- and Mathlib has no simp lemma for the former.
    | tmul s a => rfl
  obtain ⟨z, hz⟩ := (ρ.symmetricAlgebra.invariantsBaseChangeEquiv (A := S)).surjective ⟨_, hy'⟩
  have hz' := congrArg Subtype.val hz
  rw [coe_invariantsBaseChangeEquiv] at hz'
  refine ⟨r.lTensor S z, ?_⟩
  rw [hr, hz']
  exact e.apply_symm_apply y

/-- **Polynomial invariants commute with flat scalar extension.** For a finite group `G` and a
flat `R`-algebra `S`, the scalar extension of the invariant subalgebra `Sym(M)^G` is the invariant
subalgebra of the scalar-extended representation. The equivalence is the scalar extension of the
inclusion `Sym(M)^G → Sym M`, followed by the canonical equivalence
`S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`. -/
noncomputable def symmetricAlgebraInvariantsBaseChangeEquiv :
    S ⊗[R] ρ.symmetricAlgebraInvariants ≃ₐ[S] (ρ.baseChange S).symmetricAlgebraInvariants :=
  (AlgEquiv.ofInjective
    ((scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom.comp
      (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val))
    ((scalarTensorBialgEquiv (k := R) (K := S) (M := M)).injective.comp <|
      Module.Flat.lTensor_preserves_injective_linearMap
        ρ.symmetricAlgebraInvariants.val.toLinearMap Subtype.val_injective)).trans <|
    Subalgebra.equivOfEq _ _ <| le_antisymm
      (fun _ ⟨x, hx⟩ ↦ hx ▸ ρ.scalarTensorBialgEquiv_lTensor_val_mem_symmetricAlgebraInvariants x)
      fun _ hy ↦ ρ.exists_scalarTensorBialgEquiv_lTensor_val_eq hy

/-- The flat base change of the invariant subalgebra is the scalar extension of the inclusion of
the invariants, followed by the canonical equivalence `S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsBaseChangeEquiv (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    (ρ.symmetricAlgebraInvariantsBaseChangeEquiv x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x) :=
  (rfl)

end Invariants

section Reynolds

variable [CommRing R] [CommRing S] [Algebra R S] [Group G] [AddCommGroup M] [Module R M]
variable (ρ : Representation R G M) [Fintype G] [Invertible (Fintype.card G : R)]
  [Invertible (Fintype.card G : S)]

/-- **The Reynolds operator commutes with scalar extension.** Under the canonical equivalence
`S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`, the Reynolds operator of the scalar-extended representation is
the scalar extension of the Reynolds operator of `ρ`. No flatness of `S` is needed. -/
theorem coe_symmetricAlgebraReynolds_scalarTensorBialgEquiv_tmul (s : S)
    (p : SymmetricAlgebra R M) :
    ((ρ.baseChange S).symmetricAlgebraReynolds
        (scalarTensorBialgEquiv (k := R) (K := S) (s ⊗ₜ[R] p)) : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        (s ⊗ₜ[R] (ρ.symmetricAlgebraReynolds p : SymmetricAlgebra R M)) := by
  have h := (ρ.symmetricAlgebraBaseChangeEquiv S).toIntertwiningMap.map_averageMap (s ⊗ₜ[R] p)
  rw [averageMap_baseChange, LinearMap.baseChange_tmul] at h
  simpa only [coe_symmetricAlgebraReynolds, Equiv.coe_toIntertwiningMap,
    symmetricAlgebraBaseChangeEquiv_apply] using h.symm

end Reynolds

section Field

variable {K L : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] [Group G] [Finite G]
  [AddCommGroup M] [Module K M]
variable (ρ : Representation K G M)

/-- The degree-`n` part of `Representation.symmetricAlgebraBaseChangeEquiv`: the scalar extension
of the representation on `Symⁿ M` is the representation on `Symⁿ (L ⊗[K] M)`. -/
private noncomputable def symmetricAlgebraHomogeneousBaseChangeEquiv (n : ℕ) :
    ((ρ.symmetricAlgebraHomogeneous n).baseChange L).Equiv
      ((ρ.baseChange L).symmetricAlgebraHomogeneous n) :=
  .mk (homogeneousSubmoduleEquivBaseChange n).symm fun g ↦ by
    refine TensorProduct.AlgebraTensorModule.ext fun s p ↦ Subtype.ext ?_
    have h := IntertwiningMap.isIntertwining _ _
      (ρ.symmetricAlgebraBaseChangeEquiv L).toIntertwiningMap g (s ⊗ₜ[K] (p : SymmetricAlgebra K M))
    simp only [Equiv.coe_toIntertwiningMap, symmetricAlgebraBaseChangeEquiv_apply,
      baseChange_apply, LinearMap.baseChange_tmul] at h
    simpa using h

/-- **The Hilbert series of polynomial invariants is unchanged by scalar extension.** For a finite
group acting on a vector space `M` over a field `K` and a nontrivial commutative `K`-algebra `L`,
the degree-`n` part of the invariant subalgebra of `Sym (L ⊗[K] M)` has the same dimension over
`L` as the degree-`n` part of `Sym(M)^G` has over `K`. -/
theorem finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule (n : ℕ) :
    Module.finrank L ↥(Subalgebra.toSubmodule (ρ.baseChange L).symmetricAlgebraInvariants ⊓
        homogeneousSubmodule L (L ⊗[K] M) n) =
      Module.finrank K
        ↥(Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule K M n) := by
  rw [← finrank_invariants_symmetricAlgebraHomogeneous,
    ← finrank_invariants_symmetricAlgebraHomogeneous,
    ← (ρ.symmetricAlgebraHomogeneousBaseChangeEquiv n).invariantsLinearEquiv.finrank_eq,
    ← ((ρ.symmetricAlgebraHomogeneous n).invariantsBaseChangeEquiv (A := L)).finrank_eq]
  -- Instance search does not find that subspaces of `Symⁿ M` are free over the field `K`.
  have := Module.Free.of_divisionRing K (ρ.symmetricAlgebraHomogeneous n).invariants
  exact Module.finrank_baseChange

end Field

end Representation
