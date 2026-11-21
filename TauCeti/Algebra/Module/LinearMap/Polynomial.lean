/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.LinearAlgebra.Determinant.Quotient

/-!
# The determinant polynomial of a linear family of endomorphisms

Let `L` and `M` be modules over a commutative ring `R`, with `M` finite free, let
`φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms, and let `b` be a basis of `L`
indexed by a finite type `ι`. The **determinant polynomial** `LinearMap.detPoly φ b` is the
determinant of the generic element `∑ i, X i • φ (b i)` of the family: a polynomial in the
coordinates `X i`, which evaluates at the coordinates of any `x : L` to `det (φ x)`.

For an order `O` acting on a module `M` this is the polynomial `Det_{O|M}` of Kottwitz and Lan,
whose equality with a fixed reference polynomial is the determinant condition on the Lie algebra of
an abelian scheme with `O`-action. Unlike the trace `x ↦ tr (φ x)`, it distinguishes modules in
positive characteristic: over a field of characteristic `p`, the module `M^p` has trace map `0`,
like the zero module, but determinant polynomial that of `M` raised to the power `p`.

It is defined as `(-1) ^ finrank R M` times the constant coefficient of Mathlib's generic
characteristic polynomial `LinearMap.polyCharpoly φ b`, and characterized by the following facts.

## Main results

* `LinearMap.eval_detPoly`: `detPoly φ b` evaluates at the coordinates of `x : L` to
  `det (φ x)`.
* `LinearMap.aeval_detPoly`: in any commutative `R`-algebra `A`, `detPoly φ b` evaluates at
  `c : ι → A` to the determinant of `∑ i, c i • φ (b i)` on `A ⊗[R] M`;
  `LinearMap.detPoly_eq_det_sum_X_smul` is the case of the generic point over `MvPolynomial ι R`.
* `LinearMap.detPoly_baseChange`: the determinant polynomial commutes with base change.
* `LinearMap.bind₁_detPoly`: a change of basis of `L` substitutes the coordinates of the new
  generic element, as for `LinearMap.polyCharpoly` (`LinearMap.polyCharpoly_map_bind₁`).
* `LinearMap.detPoly_congr`: families intertwined by a linear equivalence have the same
  determinant polynomial; `LinearMap.detPoly_of_subsingleton`: on a subsingleton module it is `1`.
* `LinearMap.isHomogeneous_detPoly`: `detPoly φ b` is homogeneous of degree `finrank R M`.
* `LinearMap.detPoly_eq_mul_of_exact`: the determinant polynomial is multiplicative in short
  exact sequences of free modules with compatible families.
* `LinearMap.detPoly_smulRight_id`: a family acting through scalars `f x` has determinant
  polynomial the `finrank R M`-th power of the linear form `∑ i, f (b i) X i`.

## References

* R. E. Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer. Math. Soc. 5
  (1992), §5, p. 389, for the polynomial `f` and the determinant condition.
* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, London Math. Soc.
  Monographs 36 (2013), Definition 1.1.2.17, p. 19, for `Det_{O|M}`, and Remark 1.1.2.11, p. 14,
  for why traces do not suffice in positive characteristic.
-/

public section

open Module MvPolynomial

namespace LinearMap

variable {R L M ι ι' : Type*} [CommRing R] [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  (φ : L →ₗ[R] Module.End R M) (b : Basis ι R L)

/-- **Change of basis for the generic characteristic polynomial.** For a second basis `b'` of `L`,
`polyCharpoly φ b'` is obtained from `polyCharpoly φ b` by substituting for each coordinate `X i`
the `i`-th coordinate, with respect to `b`, of the generic element `∑ j, X j • b' j`.

The substitution argument is adapted from the proof of
`LinearMap.polyCharpoly_coeff_eq_zero_of_basis` in Mathlib's
`Mathlib.Algebra.Module.LinearMap.Polynomial`. -/
theorem polyCharpoly_map_bind₁ (b' : Basis ι' R L) :
    (polyCharpoly φ b).map (bind₁ (LinearMap.id.toMvPolynomial b' b)) = polyCharpoly φ b' := by
  classical
  let bₘ := Free.chooseBasis R M
  rw [polyCharpoly_eq_of_basis φ b bₘ, polyCharpoly_eq_of_basis φ b' bₘ, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun q ↦ ?_
  have : toMvPolynomial b' bₘ.end φ =
      fun i ↦ bind₁ (LinearMap.id.toMvPolynomial b' b) (toMvPolynomial b bₘ.end φ i) :=
    funext <| toMvPolynomial_comp b' b _ φ LinearMap.id
  simp [this, bind₁_bind₁]

/-- The **determinant polynomial** `Det_{O|M}` of a linear family `φ : L →ₗ[R] Module.End R M`
with respect to a basis `b` of `L`: the determinant of the generic element `∑ i, X i • φ (b i)`
(`LinearMap.detPoly_eq_det_sum_X_smul`). It is `(-1) ^ finrank R M` times the constant
coefficient of the generic characteristic polynomial `LinearMap.polyCharpoly φ b`. -/
noncomputable def detPoly : MvPolynomial ι R :=
  (-1) ^ finrank R M * (polyCharpoly φ b).coeff 0

theorem detPoly_def : detPoly φ b = (-1) ^ finrank R M * (polyCharpoly φ b).coeff 0 := (rfl)

/-- The determinant polynomial evaluates at the coordinates of `x` to the determinant of
`φ x`. -/
@[simp]
theorem eval_detPoly (x : L) : eval (b.repr x) (detPoly φ b) = (φ x).det := by
  simp [detPoly_def, polyCharpoly_coeff_eval, det_eq_sign_charpoly_coeff]

/-- The determinant polynomial evaluates at `c : ι → R` to the determinant of `φ` at the vector
with coordinates `c`. -/
theorem eval_detPoly_eq_det (c : ι → R) :
    eval c (detPoly φ b) = (φ (b.equivFun.symm c)).det := by
  have hc : ⇑(b.repr (b.equivFun.symm c)) = c := funext fun i ↦ by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← eval_detPoly φ b, hc]

/-- At the coordinates of `-x`, the determinant polynomial takes the value at `0` of the
characteristic polynomial of `φ x`; the two signs `(-1) ^ finrank R M` cancel. -/
theorem eval_detPoly_neg_eq_charpoly_eval_zero (x : L) :
    eval (b.repr (-x)) (detPoly φ b) = (φ x).charpoly.eval 0 := by
  have h : (-φ x).det = (-1) ^ finrank R M * (φ x).det := by
    simpa using det_smul (-1 : R) (φ x)
  rw [eval_detPoly, map_neg, h, det_eq_sign_charpoly_coeff]
  simp [Polynomial.coeff_zero_eq_eval_zero, ← mul_assoc, ← mul_pow]

/-- The determinant polynomial is homogeneous of degree `finrank R M`. -/
theorem isHomogeneous_detPoly : (detPoly φ b).IsHomogeneous (finrank R M) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · rw [Subsingleton.elim (detPoly φ b) 0]
    exact isHomogeneous_zero _ _ _
  have h := polyCharpoly_coeff_isHomogeneous φ b 0 (finrank R M) (zero_add _)
  rw [detPoly_def]
  rcases neg_one_pow_eq_or (MvPolynomial ι R) (finrank R M) with h1 | h1 <;> rw [h1]
  · simpa using h
  · simpa using h.neg

/-- **Independence of the basis.** For a second basis `b'` of `L`, `detPoly φ b'` is obtained from
`detPoly φ b` by substituting for each coordinate `X i` the `i`-th coordinate, with respect to `b`,
of the generic element `∑ j, X j • b' j`. -/
theorem bind₁_detPoly (b' : Basis ι' R L) :
    bind₁ (LinearMap.id.toMvPolynomial b' b) (detPoly φ b) = detPoly φ b' := by
  rw [detPoly_def, detPoly_def, ← polyCharpoly_map_bind₁ φ b b', Polynomial.coeff_map]
  simp

open Algebra.TensorProduct in
/-- **Base change.** The determinant polynomial of the base change of `φ` to a commutative
`R`-algebra `A`, with respect to the base-changed basis, is the image of `detPoly φ b` under
`algebraMap R A`. -/
theorem detPoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    detPoly (tensorProduct R A M M ∘ₗ φ.baseChange A) (basis A b) =
      MvPolynomial.map (algebraMap R A) (detPoly φ b) := by
  nontriviality A
  have := (algebraMap R A).domain_nontrivial
  rw [detPoly_def, detPoly_def, polyCharpoly_baseChange, Polynomial.coeff_map, finrank_baseChange]
  simp

/-- **Evaluation in an algebra.** In a commutative `R`-algebra `A`, the determinant polynomial
evaluates at `c : ι → A` to the determinant over `A` of the element `∑ i, c i • φ (b i)` of the
family, acting on `A ⊗[R] M`. -/
theorem aeval_detPoly (A : Type*) [CommRing A] [Algebra R A] (c : ι → A) :
    aeval c (detPoly φ b) = (∑ i, c i • (φ (b i)).baseChange A).det := by
  rw [aeval_def, ← eval_map, ← detPoly_baseChange, eval_detPoly_eq_det]
  congr 1
  ext x
  simp [Basis.equivFun_symm_apply, TensorProduct.liftAux_tmul]

/-- The determinant polynomial is the determinant of the generic element `∑ i, X i • φ (b i)` of
the family, acting on `MvPolynomial ι R ⊗[R] M`. -/
theorem detPoly_eq_det_sum_X_smul :
    detPoly φ b =
      (∑ i, (X i : MvPolynomial ι R) • (φ (b i)).baseChange (MvPolynomial ι R)).det := by
  rw [← aeval_detPoly, aeval_X_left_apply]

/-- The determinant polynomial of a family of endomorphisms of a subsingleton module is `1`. -/
theorem detPoly_of_subsingleton [Subsingleton M] : detPoly φ b = 1 := by
  rw [detPoly_eq_det_sum_X_smul]
  exact det_eq_one_of_subsingleton _

/-- **Invariance under isomorphism.** Families of endomorphisms intertwined by a linear equivalence
`e : M ≃ₗ[R] N` have the same determinant polynomial. -/
theorem detPoly_congr {N : Type*} [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] {ψ : L →ₗ[R] Module.End R N} (e : M ≃ₗ[R] N)
    (h : ∀ x, e.toLinearMap ∘ₗ φ x = ψ x ∘ₗ e.toLinearMap) :
    detPoly φ b = detPoly ψ b := by
  have hψ : ∀ x, ψ x = e.toLinearMap ∘ₗ φ x ∘ₗ e.symm.toLinearMap := fun x ↦ by
    ext m
    simpa using (LinearMap.congr_fun (h x) (e.symm m)).symm
  simp only [detPoly_eq_det_sum_X_smul, hψ]
  rw [← det_conj _ (e.baseChange R (MvPolynomial ι R) M N)]
  congr 1
  ext m
  simp [baseChange_comp]

/-- **Scalar families.** If `L` acts on `M` through scalars, by `x ↦ f x • id` for a linear form
`f`, the determinant polynomial is the `finrank R M`-th power of the linear form
`∑ i, f (b i) X i`. -/
theorem detPoly_smulRight_id (f : L →ₗ[R] R) :
    detPoly (f.smulRight (LinearMap.id : Module.End R M)) b =
      (∑ i, C (f (b i)) * X i) ^ finrank R M := by
  nontriviality R
  rw [detPoly_eq_det_sum_X_smul]
  have : ∑ i, (X i : MvPolynomial ι R) •
      ((f.smulRight (LinearMap.id : Module.End R M)) (b i)).baseChange (MvPolynomial ι R) =
      (∑ i, C (f (b i)) * X i) • LinearMap.id := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [baseChange_smul, ← smul_eq_C_mul, smul_comm (X i : MvPolynomial ι R)]
  rw [this, det_smul, det_id, mul_one, finrank_baseChange]

/-- **Multiplicativity in short exact sequences.** Let `0 → M' → M → M'' → 0` be a short exact
sequence of finite free modules, given by an injective `i`, a surjective `p` and
`Function.Exact i p`, and let `φ'`, `φ` and `φ''` be linear families of endomorphisms of the three
terms intertwined by `i` and `p`. Then `detPoly φ b = detPoly φ' b * detPoly φ'' b`. -/
theorem detPoly_eq_mul_of_exact {M' M'' : Type*} [AddCommGroup M'] [Module R M'] [Module.Free R M']
    [Module.Finite R M'] [AddCommGroup M''] [Module R M''] [Module.Free R M''] [Module.Finite R M'']
    {φ' : L →ₗ[R] Module.End R M'} {φ'' : L →ₗ[R] Module.End R M''}
    {i : M' →ₗ[R] M} {p : M →ₗ[R] M''} (hi : Function.Injective i) (hip : Function.Exact i p)
    (hp : Function.Surjective p) (hφ' : ∀ x, φ x ∘ₗ i = i ∘ₗ φ' x)
    (hφ'' : ∀ x, p ∘ₗ φ x = φ'' x ∘ₗ p) :
    detPoly φ b = detPoly φ' b * detPoly φ'' b := by
  -- Compare the determinants of the generic elements over the flat algebra `MvPolynomial ι R`,
  -- along the base change of the sequence, which stays short exact.
  simp only [detPoly_eq_det_sum_X_smul]
  set A := MvPolynomial ι R
  refine det_eq_det_mul_det_of_exact (i := i.baseChange A) (p := p.baseChange A) ?_ ?_ ?_ ?_ ?_
  · rw [baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap i hi
  · rw [baseChange_eq_lTensor, baseChange_eq_lTensor]
    exact lTensor_exact A hip hp
  · rw [baseChange_eq_lTensor]
    exact lTensor_surjective A hp
  · ext m
    simp [← comp_apply (φ _) i, hφ']
  · ext m
    simp [← comp_apply p (φ _), hφ'']

end LinearMap
