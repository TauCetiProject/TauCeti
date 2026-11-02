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

Multiplication of symmetric-algebra generators identifies the symmetric tensor power of any
module with the homogeneous component of the same degree. Injectivity comes from a left inverse:
the generators act on the symmetric tensors of all degrees by commuting multiplication operators,
so the symmetric algebra acts there as well. For a free module the identification sends the
symmetric tensor basis to the monomial basis. This identifies the quotient-tensor and polynomial
descriptions of symmetric powers, allowing constructions on symmetric tensors to be used
degreewise on the symmetric algebra.

The scalar semiring lies in `Type` because Mathlib's `SymmetricPower R ι M` requires `R` and
`ι` to share a universe, and `Sym[R]^n M` uses `ι = Fin n`. This is also the universe
convention of `Module.Basis.symmetricPower`, used in the basis comparison below.
The module and its basis index type have independent universes.

## Main declarations

* `TauCeti.SymmetricPower.toSymmetricAlgebra` multiplies the generators of a pure symmetric tensor.
* `TauCeti.SymmetricPower.toHomogeneous` restricts multiplication to its homogeneous component.
* `TauCeti.SymmetricPower.equivHomogeneous` is the resulting equivalence.

## References

The multiplication map and its basis comparison are adapted from the closed Tau Ceti PR
https://github.com/TauCetiProject/TauCeti/pull/18162 (feat: construct degreewise PBW
symmetrization).
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricPower

open _root_.SymmetricPower

universe v w

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
  apply LinearMap.apply_mem_of_forall_symmetricPower_tprod
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

/-! ### A left inverse of multiplication

The generators act on the symmetric tensors of all degrees by commuting multiplication
operators, so the symmetric algebra acts there too. Acting on the degree-zero unit tensor and
reading off degree `n` gives a left inverse of multiplication on `Sym[R]^n M`, with no
assumption on `M`. -/

/-- The symmetric tensors of all degrees, on which generators act by multiplication. -/
private abbrev AllDegrees := ∀ k : ℕ, Sym[R]^k M

private noncomputable def shiftComponent (m : M) : (j : ℕ) → AllDegrees R M →ₗ[R] Sym[R]^j M
  | 0 => 0
  | k + 1 => consMul R M k m ∘ₗ LinearMap.proj k

/-- Multiplication by a generator, raising the degree of every symmetric tensor by one. -/
private noncomputable def shiftMul : M →ₗ[R] Module.End R (AllDegrees R M) where
  toFun m := LinearMap.pi (shiftComponent R M m)
  map_add' m m' := by
    ext f j
    cases j <;> simp [shiftComponent]
  map_smul' c m := by
    ext f j
    cases j <;> simp [shiftComponent]

private theorem shiftMul_comm (m m' : M) :
    shiftMul R M m * shiftMul R M m' = shiftMul R M m' * shiftMul R M m := by
  ext f j
  rcases j with _ | _ | k
  · simp [shiftMul, shiftComponent]
  · simp [shiftMul, shiftComponent]
  · simp [shiftMul, shiftComponent, consMul_comm]

private theorem shiftMul_single (m : M) (k : ℕ) (x : Sym[R]^k M) :
    shiftMul R M m (Pi.single (M := fun k ↦ Sym[R]^k M) k x) =
      Pi.single (M := fun k ↦ Sym[R]^k M) (k + 1) (consMul R M k m x) := by
  funext j
  rcases j with _ | j
  · simp [shiftMul, shiftComponent]
  · by_cases h : j = k
    · subst h
      simp [shiftMul, shiftComponent]
    · simp [shiftMul, shiftComponent, Pi.single_eq_of_ne h,
        Pi.single_eq_of_ne (Nat.succ_ne_succ_iff.mpr h)]

private noncomputable def shiftMulAdjoin :
    M →ₗ[R] Algebra.adjoin R (Set.range (shiftMul R M)) :=
  (shiftMul R M).codRestrict (Subalgebra.toSubmodule (Algebra.adjoin R (Set.range (shiftMul R M))))
    fun m ↦ Algebra.subset_adjoin (Set.mem_range_self m)

open scoped IsMulCommutative in
/-- Generators act on symmetric tensors of all degrees by commuting multiplication operators. -/
private noncomputable def shiftAlgHom :
    SymmetricAlgebra R M →ₐ[R] Algebra.adjoin R (Set.range (shiftMul R M)) :=
  haveI := Algebra.isMulCommutative_adjoin R (s := Set.range (shiftMul R M)) <| by
    rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩ -
    exact shiftMul_comm R M m m'
  SymmetricAlgebra.lift (shiftMulAdjoin R M)

private theorem coe_shiftAlgHom_ι (m : M) :
    (shiftAlgHom R M (SymmetricAlgebra.ι R M m) : Module.End R (AllDegrees R M)) =
      shiftMul R M m := by
  simp only [shiftAlgHom, SymmetricAlgebra.lift_ι_apply]
  rfl

/-- The degree-zero unit tensor, on which the generators act. -/
private noncomputable def unitTensor : AllDegrees R M :=
  Pi.single (M := fun k ↦ Sym[R]^k M) 0 (⨂ₛ[R] i : Fin 0, (isEmptyElim i : M))

private theorem shiftAlgHom_prod_ι_unitTensor (n : ℕ) (m : Fin n → M) :
    (shiftAlgHom R M (∏ i, SymmetricAlgebra.ι R M (m i)) : Module.End R (AllDegrees R M))
        (unitTensor R M) =
      Pi.single (M := fun k ↦ Sym[R]^k M) n (⨂ₛ[R] i, m i) := by
  induction n with
  | zero => simp [unitTensor, Subsingleton.elim m isEmptyElim]
  | succ n ih =>
    rw [Fin.prod_univ_succ, map_mul, Subalgebra.coe_mul, Module.End.mul_apply, ih,
      coe_shiftAlgHom_ι, shiftMul_single, consMul_tprod, ← Fin.tail_def, Fin.cons_self_tail]

/-- Extraction of the degree-`n` symmetric tensor from the symmetric algebra: a left inverse of
multiplication. -/
private noncomputable def ofSymmetricAlgebra (n : ℕ) :
    SymmetricAlgebra R M →ₗ[R] Sym[R]^n M :=
  LinearMap.proj n ∘ₗ LinearMap.applyₗ (unitTensor R M) ∘ₗ
    (Algebra.adjoin R (Set.range (shiftMul R M))).val.toLinearMap ∘ₗ
      (shiftAlgHom R M).toLinearMap

private theorem ofSymmetricAlgebra_comp_toSymmetricAlgebra (n : ℕ) :
    ofSymmetricAlgebra R M n ∘ₗ toSymmetricAlgebra R M n = LinearMap.id := by
  refine SymmetricPower.ext fun m ↦ ?_
  simp [ofSymmetricAlgebra, shiftAlgHom_prod_ι_unitTensor]

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
  have hexp : (_root_.Sym.equivFinsuppDegree κ n (TauCeti.Sym.ofFn f)).1 =
      (List.ofFn f : Multiset κ).toFinsupp := by
    rw [_root_.Sym.coe_equivFinsuppDegree_apply, TauCeti.Sym.coe_ofFn]
  rw [hexp]
  simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, Function.comp_def] using
    TauCeti.prod_map_X_eq_monomial (R := R) (List.ofFn f : Multiset κ)

/-- Multiplication embeds the symmetric tensor power of any module into its symmetric algebra,
over any commutative semiring. -/
theorem toSymmetricAlgebra_injective (n : ℕ) :
    Function.Injective (toSymmetricAlgebra R M n) :=
  Function.LeftInverse.injective (g := ofSymmetricAlgebra R M n)
    (LinearMap.congr_fun (ofSymmetricAlgebra_comp_toSymmetricAlgebra R M n))

/-- The symmetric tensor power of a module is canonically its degree-`n` homogeneous
symmetric-algebra component. -/
noncomputable def equivHomogeneous (n : ℕ) :
    Sym[R]^n M ≃ₗ[R] TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by
  refine LinearEquiv.ofBijective (toHomogeneous R M n) ⟨?_, ?_⟩
  · intro x y h
    exact toSymmetricAlgebra_injective n (congrArg Subtype.val h)
  · intro p
    obtain ⟨x, hx⟩ := (range_toSymmetricAlgebra R M n).ge p.property
    exact ⟨x, Subtype.ext hx⟩

/-- The homogeneous equivalence has multiplication as its underlying map. -/
@[simp]
theorem coe_equivHomogeneous_apply (n : ℕ) (x : Sym[R]^n M) :
    (equivHomogeneous (R := R) (M := M) n x : SymmetricAlgebra R M) =
      toSymmetricAlgebra R M n x :=
  (rfl)

/-- The linear map underlying the homogeneous equivalence is homogeneous multiplication. -/
@[simp]
theorem toLinearMap_equivHomogeneous (n : ℕ) :
    (equivHomogeneous (R := R) (M := M) n).toLinearMap = toHomogeneous R M n := by
  rfl

/-- The homogeneous equivalence sends a pure symmetric tensor to its product of generators. -/
@[simp]
theorem equivHomogeneous_tprod (n : ℕ) (m : Fin n → M) :
    equivHomogeneous (R := R) (M := M) n (⨂ₛ[R] i, m i) =
      ⟨∏ i, SymmetricAlgebra.ι R M (m i), by
        simpa only [toSymmetricAlgebra_tprod] using
          toSymmetricAlgebra_mem_homogeneousSubmodule R M n (⨂ₛ[R] i, m i)⟩ := by
  apply Subtype.ext
  exact toSymmetricAlgebra_tprod R M n m

/-- The inverse homogeneous equivalence sends a product of generators to its pure tensor. -/
@[simp]
theorem equivHomogeneous_symm_prod_ι (n : ℕ) (m : Fin n → M)
    (h : ∏ i, SymmetricAlgebra.ι R M (m i) ∈
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n) :
    (equivHomogeneous (R := R) (M := M) n).symm ⟨∏ i, SymmetricAlgebra.ι R M (m i), h⟩ =
      ⨂ₛ[R] i, m i := by
  apply (equivHomogeneous (R := R) (M := M) n).injective
  simp only [LinearEquiv.apply_symm_apply, equivHomogeneous_tprod]

end TauCeti.SymmetricPower
