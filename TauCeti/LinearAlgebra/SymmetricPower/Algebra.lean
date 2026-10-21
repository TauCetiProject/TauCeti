/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.Basis
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import TauCeti.Algebra.MvPolynomial.Monomial

/-!
# Symmetric powers as homogeneous symmetric polynomials

Multiplication of symmetric-algebra generators identifies the symmetric tensor power of a free
module with the homogeneous component of the same degree. This identifies the quotient-tensor
and polynomial descriptions of symmetric powers, allowing constructions on symmetric tensors
to be used degreewise on the symmetric algebra.

The scalar semiring lies in `Type` because Mathlib's `SymmetricPower R ι M` requires `R` and
`ι` to share a universe, and `Sym[R]^n M` uses `ι = Fin n`. This is also the universe
convention of `Module.Basis.symmetricPower`, used in the homogeneous comparison below.
The module and its basis index type have independent universes.

## Main declarations

* `TauCeti.SymmetricPower.toSymmetricAlgebra` multiplies the generators of a pure symmetric tensor.
* `TauCeti.SymmetricPower.toHomogeneous` restricts multiplication to its homogeneous component.
* `TauCeti.SymmetricPower.equivHomogeneous` is the resulting equivalence for a free module.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricPower

open _root_.SymmetricPower

universe u v w

/-- A linear map sends every symmetric tensor into a submodule if it does so on pure tensors. -/
theorem map_mem_of_forall_tprod {R ι : Type u} {M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : Sym[R] ι M →ₗ[R] N) (p : Submodule R N)
    (h : ∀ m : ι → M, f (⨂ₛ[R] i, m i) ∈ p) (x : Sym[R] ι M) : f x ∈ p := by
  have hle : (⊤ : Submodule R (Sym[R] ι M)) ≤ p.comap f := by
    rw [← span_tprod_eq_top R ι M, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact h m
  exact hle Submodule.mem_top

variable (R : Type) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

private noncomputable def algebraMultilinear (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ M) (SymmetricAlgebra R M) :=
  (MultilinearMap.mkPiAlgebra R (Fin n) (SymmetricAlgebra R M)).compLinearMap
    (fun _ ↦ SymmetricAlgebra.ι R M)

private theorem algebraMultilinear_invariant (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (algebraMultilinear R M n).domDomCongr e = algebraMultilinear R M n := by
  ext m
  exact Equiv.prod_comp e (fun i ↦ SymmetricAlgebra.ι R M (m i))

/-- Multiplication of the canonical generators, descended to the symmetric tensor power. -/
noncomputable def toSymmetricAlgebra (n : ℕ) : Sym[R]^n M →ₗ[R] SymmetricAlgebra R M :=
  lift (algebraMultilinear R M n) (algebraMultilinear_invariant R M n)

/-- A pure symmetric tensor maps to the product of its generators. -/
@[simp]
theorem toSymmetricAlgebra_tprod (n : ℕ) (m : Fin n → M) :
    toSymmetricAlgebra R M n (⨂ₛ[R] i, m i) = ∏ i, SymmetricAlgebra.ι R M (m i) := by
  simp [toSymmetricAlgebra, algebraMultilinear]

/-- Multiplication preserves the degree of a symmetric tensor. -/
theorem toSymmetricAlgebra_mem_homogeneousSubmodule (n : ℕ) (x : Sym[R]^n M) :
    toSymmetricAlgebra R M n x ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by
  apply map_mem_of_forall_tprod
  intro m
  rw [toSymmetricAlgebra_tprod]
  simpa only [List.length_ofFn, List.map_ofFn, List.prod_ofFn, Function.comp_def] using
    TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule R M (List.ofFn m)

/-- Multiplication with codomain restricted to the homogeneous component of the same degree. -/
noncomputable def toHomogeneous (n : ℕ) :
    Sym[R]^n M →ₗ[R] TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n :=
  (toSymmetricAlgebra R M n).codRestrict _ (toSymmetricAlgebra_mem_homogeneousSubmodule R M n)

/-- The homogeneous multiplication map has ordinary multiplication as its underlying map. -/
@[simp]
theorem coe_toHomogeneous_apply (n : ℕ) (x : Sym[R]^n M) :
    (toHomogeneous R M n x : SymmetricAlgebra R M) = toSymmetricAlgebra R M n x :=
  (rfl)

/-- The image of multiplication is exactly the homogeneous component of the same degree. -/
theorem range_toSymmetricAlgebra (n : ℕ) :
    LinearMap.range (toSymmetricAlgebra R M n) =
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact toSymmetricAlgebra_mem_homogeneousSubmodule R M n x
  · rw [TauCeti.SymmetricAlgebra.homogeneousSubmodule_eq_span, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    subst n
    refine ⟨⨂ₛ[R] i, l.get i, ?_⟩
    rw [toSymmetricAlgebra_tprod]
    simp

variable {R M}

variable (R M) in
/-- Multiplication identifies the symmetric tensor basis with the homogeneous monomial basis. -/
theorem toSymmetricAlgebra_symmetricPower_apply {κ : Type w} (b : Module.Basis κ R M)
    (n : ℕ) (s : Sym κ n) :
    toSymmetricAlgebra R M n (b.symmetricPower n s) =
      (b.symmetricAlgebraHomogeneous n s : SymmetricAlgebra R M) := by
  classical
  obtain ⟨f, rfl⟩ := TauCeti.Sym.ofFn_surjective s
  rw [Module.Basis.symmetricPower_apply, tprodOfSym_ofFn, toSymmetricAlgebra_tprod]
  apply (SymmetricAlgebra.equivMvPolynomial b).injective
  rw [map_prod, TauCeti.SymmetricAlgebra.equivMvPolynomial_symmetricAlgebraHomogeneous_apply]
  simp only [SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [← List.prod_ofFn]
  have hexp : (TauCeti.symEquivFinsuppDegree κ n (TauCeti.Sym.ofFn f)).1 =
      (List.ofFn f : Multiset κ).toFinsupp := by
    rw [TauCeti.coe_symEquivFinsuppDegree_apply, TauCeti.Sym.coe_ofFn]
  rw [hexp]
  simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, Function.comp_def] using
    TauCeti.prod_map_X_eq_monomial (R := R) (List.ofFn f : Multiset κ)

/-- Multiplication embeds the symmetric tensor power of a free module into its symmetric
algebra, over any commutative semiring. -/
theorem toSymmetricAlgebra_injective [Module.Free R M] (n : ℕ) :
    Function.Injective (toSymmetricAlgebra R M n) := by
  let b := Module.Free.chooseBasis R M
  have heq : toSymmetricAlgebra R M n =
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n).subtype ∘ₗ
        (b.symmetricPower n).equiv (b.symmetricAlgebraHomogeneous n) (Equiv.refl _) := by
    apply (b.symmetricPower n).ext
    intro s
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    exact toSymmetricAlgebra_symmetricPower_apply R M b n s
  rw [heq]
  exact Subtype.val_injective.comp (LinearEquiv.injective _)

/-- The symmetric tensor power of a free module is canonically its degree-`n` homogeneous
symmetric-algebra component. -/
noncomputable def equivHomogeneous [Module.Free R M] (n : ℕ) :
    Sym[R]^n M ≃ₗ[R] TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by
  refine LinearEquiv.ofBijective (toHomogeneous R M n) ⟨?_, ?_⟩
  · intro x y h
    exact toSymmetricAlgebra_injective n (congrArg Subtype.val h)
  · intro p
    obtain ⟨x, hx⟩ := (range_toSymmetricAlgebra R M n).ge p.property
    exact ⟨x, Subtype.ext hx⟩

/-- The homogeneous equivalence has multiplication as its underlying map. -/
@[simp]
theorem coe_equivHomogeneous_apply [Module.Free R M] (n : ℕ) (x : Sym[R]^n M) :
    (equivHomogeneous (R := R) (M := M) n x : SymmetricAlgebra R M) =
      toSymmetricAlgebra R M n x :=
  (rfl)

/-- The linear map underlying the homogeneous equivalence is homogeneous multiplication. -/
@[simp]
theorem toLinearMap_equivHomogeneous [Module.Free R M] (n : ℕ) :
    (equivHomogeneous (R := R) (M := M) n).toLinearMap = toHomogeneous R M n := by
  rfl

/-- The homogeneous equivalence sends a pure symmetric tensor to its product of generators. -/
@[simp]
theorem equivHomogeneous_tprod [Module.Free R M] (n : ℕ) (m : Fin n → M) :
    equivHomogeneous (R := R) (M := M) n (⨂ₛ[R] i, m i) =
      ⟨∏ i, SymmetricAlgebra.ι R M (m i), by
        simpa only [toSymmetricAlgebra_tprod] using
          toSymmetricAlgebra_mem_homogeneousSubmodule R M n (⨂ₛ[R] i, m i)⟩ := by
  apply Subtype.ext
  exact toSymmetricAlgebra_tprod R M n m

/-- The inverse homogeneous equivalence sends a product of generators to its pure tensor. -/
@[simp]
theorem equivHomogeneous_symm_prod_ι [Module.Free R M] (n : ℕ) (m : Fin n → M)
    (h : ∏ i, SymmetricAlgebra.ι R M (m i) ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n) :
    (equivHomogeneous (R := R) (M := M) n).symm ⟨∏ i, SymmetricAlgebra.ι R M (m i), h⟩ =
      ⨂ₛ[R] i, m i := by
  apply (equivHomogeneous (R := R) (M := M) n).injective
  simp only [LinearEquiv.apply_symm_apply, equivHomogeneous_tprod]

end TauCeti.SymmetricPower
