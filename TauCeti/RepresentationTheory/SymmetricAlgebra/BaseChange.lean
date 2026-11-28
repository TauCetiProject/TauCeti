/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange
public import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.BaseChange.Invariants
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Reynolds
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Scalar extension of polynomial invariants

Let `ρ` be a representation of a monoid `G` on an `R`-module `M`, and let `S` be a commutative
`R`-algebra. The canonical equivalence `S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`
(`SymmetricAlgebra.scalarTensorBialgEquiv`) is equivariant: it intertwines the scalar
extension of the induced action of `G` on `Sym M` with the action induced by the scalar-extended
representation `ρ.baseChange S`. This file draws the consequences for invariants.

* For a finitely generated acting monoid and a flat extension of commutative rings `R → S`,
  the invariant subalgebra commutes with scalar extension:
  `S ⊗[R] Sym(M)^G ≃ Sym(S ⊗[R] M)^G` as `S`-algebras.
  The proof transports
  `Representation.mem_range_lTensor_subtype_iff_fixed_baseChange_of_fg` along the equivariant
  equivalence. The comparison extends the inclusion of invariants and is an algebra map.
* For a finite group with invertible `#G`, the Reynolds operator commutes with scalar extension
  without flatness: averaging over `G` is a finite sum, so it commutes with `S ⊗[R] -`
  (`Representation.averageMap_baseChange`).
* For any group, the finrank of each homogeneous component of the invariant subalgebra over
  a field `K` is unchanged under extension to a nontrivial commutative `K`-algebra.

## Main declarations

* `Representation.symmetricAlgebraBaseChangeEquiv`: the scalar extension of the induced
  representation on `Sym M` is equivalent to the representation induced by `ρ.baseChange S`.
* `Representation.symmetricAlgebraInvariantsBaseChangeMap`: the canonical algebra comparison
  for any monoid action.
* `Representation.symmetricAlgebraInvariantsBaseChangeMap_bijective_of_free`: the comparison is
  bijective for any monoid action over commutative semirings when `S` is free as an `R`-module.
* `Representation.symmetricAlgebraInvariantsBaseChangeEquiv`: the comparison as an algebra
  equivalence for a finitely generated acting monoid and flat scalar extension of commutative
  rings.
* `Representation.coe_symmetricAlgebraReynolds_scalarTensorBialgEquiv_tmul`: the Reynolds operator
  commutes with scalar extension.
* `Representation.symmetricAlgebraReynolds_scalarTensorBialgEquiv`: for flat `S`, the same
  compatibility stated through the invariant-subalgebra equivalence.
* `Representation.finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule`: the
  graded finranks for any group are preserved by scalar extension from a field to a
  nontrivial commutative algebra.

## References

* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 2.
-/

public section

open SymmetricAlgebra TensorProduct TauCeti.SymmetricAlgebra

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
      simp [(ρ.mem_symmetricAlgebraInvariants a).1 a.property g]

/-- The canonical comparison from the scalar extension of the invariant algebra of `ρ` to the
invariant algebra of the scalar-extended representation. -/
noncomputable def symmetricAlgebraInvariantsBaseChangeMap :
    S ⊗[R] ρ.symmetricAlgebraInvariants →ₐ[S] (ρ.baseChange S).symmetricAlgebraInvariants :=
  (((scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom).comp
    (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val)).codRestrict _
      (fun x ↦ by
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, BialgEquiv.coe_toAlgEquiv]
        exact ρ.scalarTensorBialgEquiv_lTensor_val_mem_symmetricAlgebraInvariants x)

/-- The comparison map is the tensor of the invariant inclusion followed by the symmetric
algebra scalar-extension equivalence. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsBaseChangeMap (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    (ρ.symmetricAlgebraInvariantsBaseChangeMap x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x) := by
  simp only [symmetricAlgebraInvariantsBaseChangeMap, AlgHom.coe_codRestrict,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, BialgEquiv.coe_toAlgEquiv]

/-- The tensored invariant-algebra inclusion acts by tensoring its underlying submodule
inclusion. -/
private theorem coe_lTensor_val_eq_lTensor_subtype :
    ⇑(Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val) =
      ⇑(ρ.symmetricAlgebraInvariants.toSubmodule.subtype.lTensor S) := by
  rw [AlgHom.coe_tensorProduct_map_id, LinearMap.baseChange_eq_lTensor,
    Subalgebra.toSubmodule_subtype]
  rfl

/-- Flat scalar extension makes the invariant algebra comparison injective. -/
theorem symmetricAlgebraInvariantsBaseChangeMap_injective [Module.Flat R S] :
    Function.Injective (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S)) := by
  rw [symmetricAlgebraInvariantsBaseChangeMap, AlgHom.injective_codRestrict]
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    ρ.symmetricAlgebraInvariants.toSubmodule.subtype Subtype.val_injective
  rw [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, ρ.coe_lTensor_val_eq_lTensor_subtype]
  exact (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.injective.comp h

private theorem symmetricAlgebraInvariantsBaseChangeMap_surjective
    (hlift : ∀ {x : S ⊗[R] SymmetricAlgebra R M},
      (∀ g, (ρ.symmetricAlgebra.baseChange S) g x = x) →
      x ∈ LinearMap.range (ρ.symmetricAlgebraInvariants.toSubmodule.subtype.lTensor S)) :
    Function.Surjective (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S)) := by
  intro y
  let e := ρ.symmetricAlgebraBaseChangeEquiv S
  have hw (g : G) : (ρ.symmetricAlgebra.baseChange S) g (e.symm y) = e.symm y := by
    have hg := IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g
      (y : SymmetricAlgebra S (S ⊗[R] M))
    rw [Equiv.coe_toIntertwiningMap,
      ((ρ.baseChange S).mem_symmetricAlgebraInvariants y).1 y.property g] at hg
    exact hg.symm
  obtain ⟨x, hx⟩ := hlift hw
  refine ⟨x, Subtype.ext ?_⟩
  rw [coe_symmetricAlgebraInvariantsBaseChangeMap, coe_lTensor_val_eq_lTensor_subtype,
    hx, ← ρ.symmetricAlgebraBaseChangeEquiv_apply]
  exact e.apply_symm_apply y

/-- If `S` is free as an `R`-module, the invariant algebra comparison is bijective for any
monoid action. -/
theorem symmetricAlgebraInvariantsBaseChangeMap_bijective_of_free [Module.Free R S] :
    Function.Bijective (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S)) :=
  ⟨ρ.symmetricAlgebraInvariantsBaseChangeMap_injective,
    ρ.symmetricAlgebraInvariantsBaseChangeMap_surjective
      (ρ.symmetricAlgebra.mem_range_lTensor_subtype_of_fixed_baseChange_of_free _
        fun v ↦ (ρ.mem_symmetricAlgebraInvariants v).2)⟩

end CommSemiring

section Invariants

variable [CommRing R] [CommRing S] [Algebra R S] [AddCommMonoid M] [Module R M]
  [Module.Flat R S] [Monoid G] [Monoid.FG G]
variable (ρ : Representation R G M)

/-- For a finitely generated monoid `G` and a flat extension of commutative rings `R → S`,
the canonical comparison identifies `S ⊗[R] Sym(M)^G` with the invariant algebra of the
scalar-extended representation. -/
noncomputable def symmetricAlgebraInvariantsBaseChangeEquiv :
    S ⊗[R] ρ.symmetricAlgebraInvariants ≃ₐ[S] (ρ.baseChange S).symmetricAlgebraInvariants :=
  AlgEquiv.ofBijective _ ⟨ρ.symmetricAlgebraInvariantsBaseChangeMap_injective,
    ρ.symmetricAlgebraInvariantsBaseChangeMap_surjective
      (fun {x} hx ↦ (ρ.symmetricAlgebra.mem_range_lTensor_subtype_iff_fixed_baseChange_of_fg
        ρ.symmetricAlgebraInvariants.toSubmodule ρ.mem_symmetricAlgebraInvariants (x := x)).2 hx)⟩

/-- For a finitely generated acting monoid and flat scalar extension, the equivalence has
underlying algebra homomorphism `Representation.symmetricAlgebraInvariantsBaseChangeMap`. -/
@[simp]
theorem symmetricAlgebraInvariantsBaseChangeEquiv_toAlgHom :
    (ρ.symmetricAlgebraInvariantsBaseChangeEquiv (S := S)).toAlgHom =
      ρ.symmetricAlgebraInvariantsBaseChangeMap :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- The flat scalar-extension equivalence applies the canonical invariant algebra comparison. -/
@[simp]
theorem symmetricAlgebraInvariantsBaseChangeEquiv_apply
    (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    ρ.symmetricAlgebraInvariantsBaseChangeEquiv x = ρ.symmetricAlgebraInvariantsBaseChangeMap x :=
  AlgEquiv.ofBijective_apply _ _ _

/-- The inverse of the flat scalar-extension equivalence cancels the canonical comparison. -/
@[simp]
theorem symmetricAlgebraInvariantsBaseChangeEquiv_symm_apply_baseChangeMap
    (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    ρ.symmetricAlgebraInvariantsBaseChangeEquiv.symm
      (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S) x) = x := by
  rw [← symmetricAlgebraInvariantsBaseChangeEquiv_apply, AlgEquiv.symm_apply_apply]

/-- The canonical comparison sends the inverse image under the flat equivalence back to the
original invariant. -/
@[simp]
theorem symmetricAlgebraInvariantsBaseChangeMap_apply_equiv_symm
    (y : (ρ.baseChange S).symmetricAlgebraInvariants) :
    ρ.symmetricAlgebraInvariantsBaseChangeMap
      (ρ.symmetricAlgebraInvariantsBaseChangeEquiv.symm y) = y := by
  rw [← symmetricAlgebraInvariantsBaseChangeEquiv_apply, AlgEquiv.apply_symm_apply]

/-- The inverse of the flat base change of the invariant subalgebra agrees, after inclusion, with
the inverse of the canonical equivalence `S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`. -/
@[simp]
theorem lTensor_val_symmetricAlgebraInvariantsBaseChangeEquiv_symm
    (y : (ρ.baseChange S).symmetricAlgebraInvariants) :
    Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val
        (ρ.symmetricAlgebraInvariantsBaseChangeEquiv.symm y) =
      (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).symm y := by
  apply (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.injective
  simp only [BialgEquiv.coe_toAlgEquiv, BialgEquiv.apply_symm_apply]
  rw [← coe_symmetricAlgebraInvariantsBaseChangeMap,
    ← symmetricAlgebraInvariantsBaseChangeEquiv_apply, AlgEquiv.apply_symm_apply]

/-- For a finitely generated monoid and a flat extension of commutative rings, every fixed vector
of the scalar-extended action on `Sym M` comes from the scalar extension of the invariant
subalgebra. -/
theorem exists_lTensor_val_eq_of_mem_invariants_baseChange {y : S ⊗[R] SymmetricAlgebra R M}
    (hy : ∀ g, (ρ.symmetricAlgebra.baseChange S) g y = y) :
    ∃ x : S ⊗[R] ρ.symmetricAlgebraInvariants,
      Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x = y := by
  obtain ⟨x, hx⟩ := (ρ.symmetricAlgebra.mem_range_lTensor_subtype_iff_fixed_baseChange_of_fg
    ρ.symmetricAlgebraInvariants.toSubmodule ρ.mem_symmetricAlgebraInvariants).2 hy
  exact ⟨x, (congrFun ρ.coe_lTensor_val_eq_lTensor_subtype x).trans hx⟩

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

/-- For a flat `R`-algebra `S`, the Reynolds operator of the scalar-extended representation
corresponds, under `Representation.symmetricAlgebraInvariantsBaseChangeEquiv`, to the scalar
extension of the Reynolds operator of `ρ`. -/
theorem symmetricAlgebraReynolds_scalarTensorBialgEquiv [Module.Flat R S]
    (x : S ⊗[R] SymmetricAlgebra R M) :
    (ρ.baseChange S).symmetricAlgebraReynolds (scalarTensorBialgEquiv (k := R) (K := S) x) =
      ρ.symmetricAlgebraInvariantsBaseChangeEquiv
        ((ρ.symmetricAlgebraReynolds.restrictScalars R).baseChange S x) := by
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s p =>
      refine Subtype.ext ?_
      rw [coe_symmetricAlgebraReynolds_scalarTensorBialgEquiv_tmul,
        symmetricAlgebraInvariantsBaseChangeEquiv_apply,
        coe_symmetricAlgebraInvariantsBaseChangeMap]
      simp only [LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]

end Reynolds

section Field

variable {K L : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] [Group G]
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

/-- For a group acting on a vector space `M` over a field `K` and a nontrivial commutative
`K`-algebra `L`, the degree-`n` invariants of `Sym (L ⊗[K] M)` have the same finrank over `L`
as the degree-`n` invariants of `Sym M` have over `K`. -/
theorem finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule (n : ℕ) :
    Module.finrank L ↥(Subalgebra.toSubmodule (ρ.baseChange L).symmetricAlgebraInvariants ⊓
        homogeneousSubmodule L (L ⊗[K] M) n) =
      Module.finrank K
        ↥(Subalgebra.toSubmodule ρ.symmetricAlgebraInvariants ⊓ homogeneousSubmodule K M n) := by
  rw [← finrank_invariants_symmetricAlgebraHomogeneous,
    ← finrank_invariants_symmetricAlgebraHomogeneous,
    ← (ρ.symmetricAlgebraHomogeneousBaseChangeEquiv n).invariantsLinearEquiv.finrank_eq,
    ← ((ρ.symmetricAlgebraHomogeneous n).invariantsBaseChangeEquivOfFree (A := L)).finrank_eq]
  -- Instance search does not find that subspaces of `Symⁿ M` are free over the field `K`.
  have := Module.Free.of_divisionRing K (ρ.symmetricAlgebraHomogeneous n).invariants
  exact Module.finrank_baseChange

end Field

end Representation
