/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Prod
public import TauCeti.RepresentationTheory.SymmetricAlgebra.BaseChange

/-!
# Polynomial invariants in the presence of fixed directions

Let `ρ` be a representation of a group `G` on an `R`-module `M`, and let `N` be an `R`-module on
which `G` acts trivially. The group then acts on `N × M` by `(trivial R G N).prod ρ`. Under the
canonical equivalence `Sym (N × M) ≃ Sym N ⊗[R] Sym M` (`SymmetricAlgebra.prodEquiv`), this action
becomes the identity on the first factor and the induced action on the second, that is, the
scalar extension of the induced representation on `Sym M` to the `R`-algebra `Sym N`.

For a finite group, and when `Sym N` is flat over `R` (for instance when `N` is free, or over a
field), taking invariants commutes with this scalar extension
(`Representation.exists_lTensor_val_eq_of_mem_invariants_baseChange`). Hence the invariant algebra
of `N × M` is

`Sym (N × M)^G ≃ Sym N ⊗[R] Sym(M)^G`.

In particular, if `Sym(M)^G` is a polynomial algebra on invariants `fᵢ`, and `N` has a basis
`bⱼ`, then `Sym (N × M)^G` is a polynomial algebra on the degree-one invariants `bⱼ` together with
the `fᵢ`, read in `Sym (N × M)` through the inclusion `M → N × M`. So fixed directions contribute
exactly one basic invariant of degree one each, and leave the other basic invariants and their
degrees unchanged. This applies to polynomial functions on a space `V = V^W ⊕ E` with a group `W`
acting trivially on `V^W`, taking `M = E*` and `N = (V^W)*`: the fixed space `V^W` contributes
degree-one generators, and only the complement `E` carries the nontrivial invariants.

## Main definitions

* `Representation.symmetricAlgebraInvariantsTrivialProdEquiv`: the algebra equivalence
  `Sym (N × M)^G ≃ Sym N ⊗[R] Sym(M)^G`.

## Main results

* `Representation.prodEquiv_symmetricAlgebra_trivial_prod`: the equivalence
  `Sym (N × M) ≃ Sym N ⊗[R] Sym M` carries the induced action of `(trivial R G N).prod ρ` to the
  scalar extension of the induced action of `ρ`.
* `Representation.coe_symmetricAlgebraInvariantsTrivialProdEquiv_symm`: the inverse equivalence
  is the inverse of `SymmetricAlgebra.prodEquiv` on `Sym N ⊗[R] Sym(M)^G`.
* `Representation.bijective_aeval_symmetricAlgebraInvariants_trivial_prod`: polynomial generators
  of `Sym(M)^G`, together with a basis of `N`, are polynomial generators of `Sym (N × M)^G`.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, CMS Books in Mathematics, Springer (2001).
* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995).
-/

public section

open TensorProduct

namespace Representation

variable {R G M N : Type*}

section CommSemiring

variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (ρ : Representation R G M)

/-- The equivalence `Sym (N × M) ≃ Sym N ⊗[R] Sym M` carries the action induced by
`(trivial R G N).prod ρ` to the identity on `Sym N` tensored with the action induced by `ρ`, that
is, to the scalar extension of `ρ.symmetricAlgebra` to the `R`-algebra `Sym N`. -/
theorem prodEquiv_symmetricAlgebra_trivial_prod (g : G) (p : SymmetricAlgebra R (N × M)) :
    SymmetricAlgebra.prodEquiv R N M (((trivial R G N).prod ρ).symmetricAlgebra g p) =
      ρ.symmetricAlgebra.baseChange (SymmetricAlgebra R N) g
        (SymmetricAlgebra.prodEquiv R N M p) := by
  have hg : ((trivial R G N).prod ρ) g = LinearMap.id.prodMap (ρ g) := by ext <;> simp
  rw [symmetricAlgebra_apply, hg, SymmetricAlgebra.prodEquiv_map_prodMap, SymmetricAlgebra.map_id]
  induction SymmetricAlgebra.prodEquiv R N M p with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q r => simp

end CommSemiring

section Invariants

variable [CommRing R] [Group G] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (ρ : Representation R G M)

/-- The scalar extension of the inclusion of the invariants, read in `Sym (N × M)`, lands in the
invariants of `(trivial R G N).prod ρ`. -/
private theorem prodEquiv_symm_lTensor_val_mem_symmetricAlgebraInvariants
    (x : SymmetricAlgebra R N ⊗[R] ρ.symmetricAlgebraInvariants) :
    (SymmetricAlgebra.prodEquiv R N M).symm
        (Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R N) (SymmetricAlgebra R N)
          ρ.symmetricAlgebraInvariants.val x) ∈
      ((trivial R G N).prod ρ).symmetricAlgebraInvariants := by
  refine (((trivial R G N).prod ρ).mem_symmetricAlgebraInvariants _).2 fun g ↦ ?_
  apply (SymmetricAlgebra.prodEquiv R N M).injective
  rw [prodEquiv_symmetricAlgebra_trivial_prod, AlgEquiv.apply_symm_apply]
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q a => simp [(ρ.mem_symmetricAlgebraInvariants a).1 a.2 g]

variable [Finite G] [Module.Flat R (SymmetricAlgebra R N)]

/-- Every invariant of `(trivial R G N).prod ρ` comes from `Sym N ⊗[R] Sym(M)^G`, when `Sym N` is
flat over `R`. -/
private theorem exists_prodEquiv_symm_lTensor_val_eq {p : SymmetricAlgebra R (N × M)}
    (hp : p ∈ ((trivial R G N).prod ρ).symmetricAlgebraInvariants) :
    ∃ x : SymmetricAlgebra R N ⊗[R] ρ.symmetricAlgebraInvariants,
      (SymmetricAlgebra.prodEquiv R N M).symm
        (Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R N) (SymmetricAlgebra R N)
          ρ.symmetricAlgebraInvariants.val x) = p := by
  -- The image of `p` in `Sym N ⊗[R] Sym M` is an invariant of the scalar extension of the
  -- induced representation, hence the scalar extension of an invariant by flatness.
  obtain ⟨x, hx⟩ := ρ.exists_lTensor_val_eq_of_mem_invariants_baseChange
    (y := SymmetricAlgebra.prodEquiv R N M p) fun g ↦ by
      rw [← prodEquiv_symmetricAlgebra_trivial_prod,
        (((trivial R G N).prod ρ).mem_symmetricAlgebraInvariants p).1 hp g]
  exact ⟨x, by rw [hx, AlgEquiv.symm_apply_apply]⟩

/-- **Fixed directions split off the polynomial invariants.** Let a finite group act on `N × M`
by `ρ` on `M` and trivially on `N`, with `Sym N` flat over `R`. Then the invariant subalgebra of
`Sym (N × M)` is `Sym N ⊗[R] Sym(M)^G`: the inverse equivalence is the inclusion of the
invariants of `M`, tensored with `Sym N`, followed by `Sym N ⊗[R] Sym M ≃ Sym (N × M)`. -/
noncomputable def symmetricAlgebraInvariantsTrivialProdEquiv :
    ((trivial R G N).prod ρ).symmetricAlgebraInvariants ≃ₐ[R]
      SymmetricAlgebra R N ⊗[R] ρ.symmetricAlgebraInvariants :=
  ((AlgEquiv.ofInjective
    ((SymmetricAlgebra.prodEquiv R N M).symm.toAlgHom.comp
      ((Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R N) (SymmetricAlgebra R N)
        ρ.symmetricAlgebraInvariants.val).restrictScalars R))
    ((SymmetricAlgebra.prodEquiv R N M).symm.injective.comp <|
      Module.Flat.lTensor_preserves_injective_linearMap
        ρ.symmetricAlgebraInvariants.val.toLinearMap Subtype.val_injective)).trans <|
    Subalgebra.equivOfEq _ _ <| le_antisymm
      (fun _ ⟨x, hx⟩ ↦ hx ▸ ρ.prodEquiv_symm_lTensor_val_mem_symmetricAlgebraInvariants x)
      fun _ hp ↦ ρ.exists_prodEquiv_symm_lTensor_val_eq hp).symm

/-- The inverse of `Representation.symmetricAlgebraInvariantsTrivialProdEquiv` is the inclusion
of the invariants of `M`, tensored with `Sym N`, followed by the inverse of
`SymmetricAlgebra.prodEquiv`. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsTrivialProdEquiv_symm
    (x : SymmetricAlgebra R N ⊗[R] ρ.symmetricAlgebraInvariants) :
    ((ρ.symmetricAlgebraInvariantsTrivialProdEquiv (N := N)).symm x :
        SymmetricAlgebra R (N × M)) =
      (SymmetricAlgebra.prodEquiv R N M).symm
        (Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R N) (SymmetricAlgebra R N)
          ρ.symmetricAlgebraInvariants.val x) :=
  (rfl)

/-- The equivalence `Representation.symmetricAlgebraInvariantsTrivialProdEquiv`, followed by the
inclusion of the invariants of `M` tensored with `Sym N`, is the restriction of
`SymmetricAlgebra.prodEquiv` to the invariants of `N × M`. -/
@[simp]
theorem lTensor_val_symmetricAlgebraInvariantsTrivialProdEquiv
    (p : ((trivial R G N).prod ρ).symmetricAlgebraInvariants) :
    Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R N) (SymmetricAlgebra R N)
        ρ.symmetricAlgebraInvariants.val (ρ.symmetricAlgebraInvariantsTrivialProdEquiv p) =
      SymmetricAlgebra.prodEquiv R N M p := by
  apply (SymmetricAlgebra.prodEquiv R N M).symm.injective
  rw [← coe_symmetricAlgebraInvariantsTrivialProdEquiv_symm, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply]

omit [Module.Flat R (SymmetricAlgebra R N)] in
/-- **Fixed directions contribute degree-one basic invariants.** Let a finite group act on
`N × M` by `ρ` on `M` and trivially on `N`. If invariants `fᵢ` are polynomial generators of
`Sym(M)^G`, and `bⱼ` is a basis of `N`, then the degree-one invariants `bⱼ` together with the
`fᵢ`, read in `Sym (N × M)` through the inclusion `M → N × M`, are polynomial generators of
`Sym (N × M)^G`. -/
theorem bijective_aeval_symmetricAlgebraInvariants_trivial_prod {κ ι : Type*}
    (b : Module.Basis κ R N) {f : ι → ρ.symmetricAlgebraInvariants}
    (hf : Function.Bijective (MvPolynomial.aeval (R := R) f))
    {F : κ ⊕ ι → ((trivial R G N).prod ρ).symmetricAlgebraInvariants}
    (hF₁ : ∀ j, (F (.inl j) : SymmetricAlgebra R (N × M)) =
      SymmetricAlgebra.ι R (N × M) (b j, 0))
    (hF₂ : ∀ i, (F (.inr i) : SymmetricAlgebra R (N × M)) =
      SymmetricAlgebra.map R (LinearMap.inr R N M) (f i)) :
    Function.Bijective (MvPolynomial.aeval (R := R) F) := by
  have : Module.Free R N := .of_basis b
  -- Identify `aeval F` with the composite of the equivalences
  -- `R[κ ⊕ ι] ≃ R[κ] ⊗ R[ι] ≃ Sym N ⊗ Sym(M)^G ≃ Sym (N × M)^G`.
  let e : MvPolynomial (κ ⊕ ι) R ≃ₐ[R] ((trivial R G N).prod ρ).symmetricAlgebraInvariants :=
    (MvPolynomial.tensorEquivSum R κ ι R).symm.trans <|
      (Algebra.TensorProduct.congr (SymmetricAlgebra.equivMvPolynomial b).symm
        (AlgEquiv.ofBijective _ hf)).trans
      (ρ.symmetricAlgebraInvariantsTrivialProdEquiv (N := N)).symm
  have he : MvPolynomial.aeval (R := R) F = e.toAlgHom := by
    refine MvPolynomial.algHom_ext fun k ↦ Subtype.ext ?_
    rcases k with j | i
    · have : (MvPolynomial.tensorEquivSum R κ ι R).symm (.X (.inl j)) = .X j ⊗ₜ 1 := by
        rw [AlgEquiv.symm_apply_eq, MvPolynomial.tensorEquivSum_X_tmul_one]
      simp [e, this, hF₁]
    · have : (MvPolynomial.tensorEquivSum R κ ι R).symm (.X (.inr i)) = 1 ⊗ₜ .X i := by
        rw [AlgEquiv.symm_apply_eq, MvPolynomial.tensorEquivSum_one_tmul_X]
      simp [e, this, hF₂]
  rw [he]
  exact e.bijective

end Invariants

end Representation
