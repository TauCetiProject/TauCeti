/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.SymmetricAlgebra.BasicInvariants
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Reynolds
import TauCeti.Algebra.TensorProduct.BaseChange
import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# Scalar extension of polynomial invariants

Let `ρ` be a representation of a group `G` on an `R`-module `M`, and let `S` be a commutative
`R`-algebra. The canonical equivalence `S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`
(`SymmetricAlgebra.scalarTensorBialgEquiv`) is equivariant: it intertwines the scalar
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
* `Representation.symmetricAlgebraInvariantsBaseChangeMap`: the canonical algebra comparison
  for any monoid action.
* `Representation.symmetricAlgebraInvariantsBaseChangeMap_bijective_of_free`: the comparison is
  bijective for any monoid action when the coefficient algebra is free.
* `Representation.IsBasicInvariants.baseChange_of_bijective`,
  `Representation.IsBasicInvariants.baseChange` and
  `Representation.IsBasicInvariants.baseChange_of_free`: basic invariants retain their degrees
  under a bijective comparison, in particular for finite-flat and free scalar extensions.
* `Representation.symmetricAlgebraInvariantsBaseChangeEquiv`: flat scalar extension of the invariant
  subalgebra, as an algebra equivalence.
* `Representation.exists_lTensor_val_eq_of_mem_invariants_baseChange`: for flat `S`, every invariant
  of the scalar extension of the induced representation on `Sym M` comes from `S ⊗[R] Sym(M)^G`.
* `Representation.coe_symmetricAlgebraReynolds_scalarTensorBialgEquiv_tmul`: the Reynolds operator
  commutes with scalar extension.
* `Representation.symmetricAlgebraReynolds_scalarTensorBialgEquiv`: for flat `S`, the same
  compatibility stated through the invariant-subalgebra equivalence.
* `Representation.finrank_symmetricAlgebraInvariants_baseChange_inf_homogeneousSubmodule`: the
  graded dimensions of the invariant subalgebra are invariant under scalar extension of fields.

## References

* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), Chapter 2.
-/

public section

open SymmetricAlgebra TensorProduct TauCeti.SymmetricAlgebra

namespace Representation

variable {R S G M ι : Type*}

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

/-- The invariant algebra comparison for scalar extension sends a tensor of invariants into the
scalar-extended invariant algebra via the canonical symmetric algebra equivalence. -/
noncomputable def symmetricAlgebraInvariantsBaseChangeMap :
    S ⊗[R] ρ.symmetricAlgebraInvariants →ₐ[S] (ρ.baseChange S).symmetricAlgebraInvariants :=
  (((scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom).comp
    (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val)).codRestrict _
      (ρ.scalarTensorBialgEquiv_lTensor_val_mem_symmetricAlgebraInvariants (S := S))

/-- The comparison map is the tensor of the invariant inclusion followed by the symmetric
algebra scalar-extension equivalence. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsBaseChangeMap (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    (ρ.symmetricAlgebraInvariantsBaseChangeMap x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x) :=
  (rfl)

/-- On a pure tensor, the invariant comparison applies the symmetric algebra equivalence to the
tensor of the scalar and the underlying invariant. -/
theorem symmetricAlgebraInvariantsBaseChangeMap_tmul (s : S)
    (a : ρ.symmetricAlgebraInvariants) :
    (ρ.symmetricAlgebraInvariantsBaseChangeMap (s ⊗ₜ[R] a) : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (s ⊗ₜ[R] (a : SymmetricAlgebra R M)) := by
  rw [coe_symmetricAlgebraInvariantsBaseChangeMap, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Subalgebra.coe_val]

/-- Flat scalar extension makes the invariant algebra comparison injective. -/
theorem symmetricAlgebraInvariantsBaseChangeMap_injective [Module.Flat R S] :
    Function.Injective (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S)) := by
  intro x y hxy
  have h := congrArg Subtype.val hxy
  simp only [coe_symmetricAlgebraInvariantsBaseChangeMap, AlgHom.coe_tensorProduct_map_id,
    LinearMap.baseChange_eq_lTensor] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap
    ρ.symmetricAlgebraInvariants.val.toLinearMap Subtype.val_injective
    (scalarTensorBialgEquiv.injective h)

/-- The invariant algebra comparison is bijective for a free scalar extension of any monoid
representation. In a basis of `S` over `R`, an invariant tensor has invariant coordinates. -/
theorem symmetricAlgebraInvariantsBaseChangeMap_bijective_of_free [Module.Free R S] :
    Function.Bijective (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S)) := by
  classical
  refine ⟨ρ.symmetricAlgebraInvariantsBaseChangeMap_injective, ?_⟩
  -- Transport the basis argument of `Representation.invariantsBaseChangeMap_surjective_of_free`
  -- through the symmetric algebra equivalence.
  intro y
  let e := ρ.symmetricAlgebraBaseChangeEquiv S
  let w := e.symm (y : SymmetricAlgebra S (S ⊗[R] M))
  have hw (g : G) : (ρ.symmetricAlgebra.baseChange S) g w = w := by
    have hg := IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g
      (y : SymmetricAlgebra S (S ⊗[R] M))
    rw [Equiv.coe_toIntertwiningMap,
      ((ρ.baseChange S).mem_symmetricAlgebraInvariants y).1 y.property g] at hg
    exact hg.symm
  let b := Module.Free.chooseBasis R S
  have hb (i : Module.Free.ChooseBasisIndex R S) :
      TensorProduct.equivFinsuppOfBasisLeft b w i ∈ ρ.symmetricAlgebraInvariants :=
    (ρ.mem_symmetricAlgebraInvariants _).2
      (equivFinsuppOfBasisLeft_apply_fixed_of_baseChange b ρ.symmetricAlgebra hw i)
  obtain ⟨x, hx⟩ :=
    (b.mem_range_lTensor_subtype_iff ρ.symmetricAlgebraInvariants.toSubmodule w).2 hb
  have hxt : ρ.symmetricAlgebraInvariants.val.toLinearMap.lTensor S x = w := by
    rw [Subalgebra.toSubmodule_subtype] at hx
    exact hx
  refine ⟨x, Subtype.ext ?_⟩
  rw [coe_symmetricAlgebraInvariantsBaseChangeMap, AlgHom.coe_tensorProduct_map_id,
    LinearMap.baseChange_eq_lTensor, hxt, ← ρ.symmetricAlgebraBaseChangeEquiv_apply]
  exact e.apply_symm_apply y

variable {ρ}

/-- If the invariant algebra comparison is bijective, the scalar extensions of basic invariants
are basic invariants of the same degrees. -/
theorem IsBasicInvariants.baseChange_of_bijective
    {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ} (h : ρ.IsBasicInvariants f d)
    (hbij : Function.Bijective (ρ.symmetricAlgebraInvariantsBaseChangeMap (S := S))) :
    (ρ.baseChange S).IsBasicInvariants
      (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeMap (1 ⊗ₜ[R] f i)) d := by
  constructor
  · intro i
    rw [symmetricAlgebraInvariantsBaseChangeMap_tmul]
    exact scalarTensorBialgEquiv_mem_homogeneousSubmodule
      (Submodule.tmul_mem_baseChange_of_mem 1 (h.homogeneous i))
  · -- The evaluation factorization uses Mathlib's `MvPolynomial.algebraTensorAlgEquiv` to
    -- change the coefficient ring.
    rw [← MvPolynomial.comp_aeval,
      MvPolynomial.aeval_one_tmul_eq_lTensor_comp_algebraTensorAlgEquiv_symm f]
    have ht : Function.Bijective (Algebra.TensorProduct.lTensor (S := S) S
        (MvPolynomial.aeval (R := R) f)) := by
      rw [AlgHom.coe_tensorProduct_map_id (S := S), ← AlgHom.coe_tensorProduct_map_id (S := R)]
      exact Algebra.TensorProduct.map_bijective
        (f := AlgHom.id R S) Function.bijective_id h.bijective_aeval
    simpa only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom] using
      hbij.comp (ht.comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R S).symm.bijective)

/-- Over a free algebra `S`, the scalar extensions of basic invariants for any monoid
are basic invariants of the same degrees. -/
theorem IsBasicInvariants.baseChange_of_free [Module.Free R S]
    {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ} (h : ρ.IsBasicInvariants f d) :
    (ρ.baseChange S).IsBasicInvariants
      (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeMap (1 ⊗ₜ[R] f i)) d :=
  h.baseChange_of_bijective ρ.symmetricAlgebraInvariantsBaseChangeMap_bijective_of_free

end CommSemiring

section Invariants

variable [CommRing R] [CommRing S] [Algebra R S] [Group G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

variable [Module.Flat R S] [Finite G]

/-- Every invariant of the scalar extension of the induced representation on `Sym M` is the
scalar extension of an invariant of `ρ`, when `S` is flat over `R`. -/
theorem exists_lTensor_val_eq_of_mem_invariants_baseChange {y : S ⊗[R] SymmetricAlgebra R M}
    (hy : y ∈ (ρ.symmetricAlgebra.baseChange S).invariants) :
    ∃ x : S ⊗[R] ρ.symmetricAlgebraInvariants,
      Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x = y := by
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
  obtain ⟨z, hz⟩ := (ρ.symmetricAlgebra.invariantsBaseChangeEquiv (A := S)).surjective ⟨y, hy⟩
  have hz' := congrArg Subtype.val hz
  rw [coe_invariantsBaseChangeEquiv] at hz'
  exact ⟨r.lTensor S z, by rw [hr, hz']⟩

/-- Every invariant of `ρ.baseChange S` is the image of the scalar extension of an invariant of
`ρ`, when `S` is flat over `R`. -/
private theorem exists_scalarTensorBialgEquiv_lTensor_val_eq
    {y : SymmetricAlgebra S (S ⊗[R] M)} (hy : y ∈ (ρ.baseChange S).symmetricAlgebraInvariants) :
    ∃ x : S ⊗[R] ρ.symmetricAlgebraInvariants, scalarTensorBialgEquiv (k := R) (K := S)
      (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x) = y := by
  -- Pull `y` back to an invariant of the scalar extension of the induced representation.
  let e := ρ.symmetricAlgebraBaseChangeEquiv S
  have hy' : e.symm y ∈ (ρ.symmetricAlgebra.baseChange S).invariants := by
    have := (e.symm.invariantsLinearEquiv ⟨y, (mem_invariants _ y).2
      (((ρ.baseChange S).mem_symmetricAlgebraInvariants y).1 hy)⟩).property
    rwa [Equiv.coe_invariantsLinearEquiv_apply] at this
  obtain ⟨x, hx⟩ := ρ.exists_lTensor_val_eq_of_mem_invariants_baseChange hy'
  refine ⟨x, ?_⟩
  rw [hx]
  exact e.apply_symm_apply y

/-- **Polynomial invariants commute with flat scalar extension.** For a finite group `G` and a
flat `R`-algebra `S`, the scalar extension of the invariant subalgebra `Sym(M)^G` is the invariant
subalgebra of the scalar-extended representation. The equivalence is the scalar extension of the
inclusion `Sym(M)^G → Sym M`, followed by the canonical equivalence
`S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`. -/
noncomputable def symmetricAlgebraInvariantsBaseChangeEquiv :
    S ⊗[R] ρ.symmetricAlgebraInvariants ≃ₐ[S] (ρ.baseChange S).symmetricAlgebraInvariants := by
  refine AlgEquiv.ofBijective _ ⟨ρ.symmetricAlgebraInvariantsBaseChangeMap_injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ρ.exists_scalarTensorBialgEquiv_lTensor_val_eq y.property
  exact ⟨x, Subtype.ext ((ρ.coe_symmetricAlgebraInvariantsBaseChangeMap x).trans hx)⟩

/-- The finite-flat equivalence has underlying algebra homomorphism
`Representation.symmetricAlgebraInvariantsBaseChangeMap`. -/
@[simp]
theorem symmetricAlgebraInvariantsBaseChangeEquiv_toAlgHom :
    (ρ.symmetricAlgebraInvariantsBaseChangeEquiv (S := S)).toAlgHom =
      ρ.symmetricAlgebraInvariantsBaseChangeMap :=
  AlgEquiv.toAlgHom_ofBijective _ _

/-- The finite-flat equivalence applies the canonical invariant algebra comparison. -/
@[simp]
theorem symmetricAlgebraInvariantsBaseChangeEquiv_apply
    (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    ρ.symmetricAlgebraInvariantsBaseChangeEquiv x = ρ.symmetricAlgebraInvariantsBaseChangeMap x :=
  AlgEquiv.ofBijective_apply _ _ _

/-- The flat base change of the invariant subalgebra is the scalar extension of the inclusion of
the invariants, followed by the canonical equivalence `S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`. -/
theorem coe_symmetricAlgebraInvariantsBaseChangeEquiv (x : S ⊗[R] ρ.symmetricAlgebraInvariants) :
    (ρ.symmetricAlgebraInvariantsBaseChangeEquiv x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S)
        (Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val x) := by
  rw [symmetricAlgebraInvariantsBaseChangeEquiv_apply, coe_symmetricAlgebraInvariantsBaseChangeMap]

/-- The inverse of the flat base change of the invariant subalgebra agrees, after inclusion, with
the inverse of the canonical equivalence `S ⊗[R] Sym M ≃ Sym (S ⊗[R] M)`. -/
@[simp]
theorem lTensor_val_symmetricAlgebraInvariantsBaseChangeEquiv_symm
    (y : (ρ.baseChange S).symmetricAlgebraInvariants) :
    Algebra.TensorProduct.lTensor (S := S) S ρ.symmetricAlgebraInvariants.val
        (ρ.symmetricAlgebraInvariantsBaseChangeEquiv.symm y) =
      (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).symm y := by
  apply (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.injective
  simp only [BialgEquiv.coe_toAlgEquiv]
  rw [← coe_symmetricAlgebraInvariantsBaseChangeEquiv, AlgEquiv.apply_symm_apply,
    BialgEquiv.apply_symm_apply]

variable {ρ}

/-- Over a flat algebra `S`, the scalar extensions of basic invariants of a finite group
are basic invariants of the same degrees. -/
theorem IsBasicInvariants.baseChange {f : ι → ρ.symmetricAlgebraInvariants} {d : ι → ℕ}
    (h : ρ.IsBasicInvariants f d) :
    (ρ.baseChange S).IsBasicInvariants
      (fun i ↦ ρ.symmetricAlgebraInvariantsBaseChangeEquiv (1 ⊗ₜ[R] f i)) d := by
  simp only [symmetricAlgebraInvariantsBaseChangeEquiv_apply]
  apply h.baseChange_of_bijective
  rw [← symmetricAlgebraInvariantsBaseChangeEquiv_toAlgHom, AlgEquiv.coe_toAlgHom]
  exact ρ.symmetricAlgebraInvariantsBaseChangeEquiv.bijective

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
        coe_symmetricAlgebraInvariantsBaseChangeEquiv]
      simp only [LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]

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
