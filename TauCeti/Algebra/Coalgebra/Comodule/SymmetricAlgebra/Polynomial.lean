/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
public import TauCeti.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.MvPolynomial.Coeff
import TauCeti.Data.Nat.Choose.Basic

/-!
# Polynomial functions on a comodule

Let `V` be a right comodule over a commutative Hopf algebra `H`, with a finite basis `b`
indexed by `ι`. The polynomial functions on `V` are the symmetric algebra of the dual comodule
`V*`. Writing them in the coordinates `X i = b*ᵢ` identifies them with `MvPolynomial ι R`, and this
file transports the comodule structure along that identification.

Concretely, the coaction is the algebra homomorphism sending the coordinate `X i` to
`∑ j, X j ⊗ S(c(b*ᵢ, b j))`, where `c(b*ᵢ, b j)` is a matrix coefficient of `V` and `S` is the
antipode. On algebra-valued points this is the contragredient action `(g • f)(v) = f(g⁻¹ v)`: a
point `g` substitutes `∑ j, g(S(c(b*ᵢ, b j))) X j` for `X i`. Every homogeneous component is a
subcomodule.

For the standard representation of `SL₂` these are the binary forms, the basic rational
representations of `SL₂`.

In two variables `x = X 0` and `y = X 1`, over a ring without zero divisors, the span of the
monomials `xⁱ yʲ` of degree `d = i + j` whose binomial coefficient `d choose i` is nonzero in `R`
is a subcomodule, for every coaction of this form. In characteristic zero it is the whole
homogeneous component; in characteristic `p` it is a proper subcomodule exactly when some
`d choose i` vanishes. The reason is the identity
`C(d, i) C(i, r) C(j, s) = C(d, r + s) C(r + s, r) C(d - r - s, j - s)`: the coaction expands
`xⁱ yʲ` into monomials `x^(r + s) y^(d - r - s)` with coefficient divisible by `C(i, r) C(j, s)`.

## Main declarations

* `TauCeti.Comodule.polynomial`: the comodule of polynomial functions on `V`, in the coordinates
  of the basis `b`.
* `TauCeti.Comodule.polynomial_coact_X`: the coaction of a coordinate function.
* `TauCeti.Comodule.polynomialCoact`: the coaction as an algebra homomorphism.
* `TauCeti.Comodule.polynomialHomogeneousSubcomodule`: the homogeneous polynomial functions of a
  fixed degree, as a subcomodule.
* `TauCeti.Comodule.polynomialBinomialSubcomodule`: in two variables, the monomials of degree `d`
  with nonzero binomial coefficient span a subcomodule.
* `TauCeti.Comodule.algebraTensorAlgEquiv_endOfPoint_polynomial`: a point acts on polynomial
  functions by the contragredient linear substitution.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.2.
* J. S. Milne, *Algebraic Groups* (2017), §4.a.
-/

public section

open Module
open scoped TensorProduct

namespace TauCeti

namespace Comodule

variable {R H V ι : Type*} [CommSemiring R] [CommSemiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V] [Fintype ι]

section Coact

variable (H) in
/-- The coaction on polynomial functions on `V`, as an algebra homomorphism: it sends the
coordinate `X i` to `∑ j, X j ⊗ S(c(b*ᵢ, b j))`. By `polynomial_coact` it is the coaction of
`polynomial H b`. -/
noncomputable def polynomialCoact (b : Basis ι R V) :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⊗[R] H :=
  MvPolynomial.aeval fun i ↦ ∑ j, MvPolynomial.X j ⊗ₜ[R]
    HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j))

@[simp]
theorem polynomialCoact_X (b : Basis ι R V) (i : ι) :
    polynomialCoact H b (MvPolynomial.X i) = ∑ j, MvPolynomial.X j ⊗ₜ[R]
      HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j)) :=
  MvPolynomial.aeval_X _ _

end Coact

variable [DecidableEq ι]

variable (H) in
/-- The comodule of polynomial functions on a comodule `V` with a finite basis `b`, in the
coordinates of `b`: the symmetric algebra of the dual comodule, transported along the
identification of `Sym(V*)` with `MvPolynomial ι R` sending `b*ᵢ` to `X i`.

This is deliberately not a global instance, since `MvPolynomial ι R` carries many coactions. -/
@[implicit_reducible]
noncomputable def polynomial (b : Basis ι R V) : Comodule R H (MvPolynomial ι R) :=
  haveI := Module.Finite.of_basis b
  haveI := Module.Projective.of_basis b
  letI := dual R H V
  letI := symmetricAlgebra R H (Module.Dual R V)
  Transport (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearEquiv

/-- The coaction of the coordinate function `X i` on polynomial functions. -/
theorem polynomial_coact_X (b : Basis ι R V) (i : ι) :
    letI := polynomial H b
    coact (R := R) (C := H) (MvPolynomial.X i : MvPolynomial ι R) =
      ∑ j, MvPolynomial.X j ⊗ₜ[R]
        HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j)) := by
  have := Module.Finite.of_basis b
  have := Module.Projective.of_basis b
  let _ := dual R H V
  let _ := symmetricAlgebra R H (Module.Dual R V)
  have he : (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearEquiv.symm
      (MvPolynomial.X i) = SymmetricAlgebra.ι R (Module.Dual R V) (b.dualBasis i) :=
    SymmetricAlgebra.equivMvPolynomial_symm_X b.dualBasis i
  rw [polynomial, transport_coact_apply, he, symmetricAlgebra_coact, AlgHom.toLinearMap_apply,
    symmetricAlgebraCoact_ι, dual_coact, dualCoact_eq_sum b, map_sum, map_sum]
  simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    AlgEquiv.toLinearEquiv_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply, LinearMap.id_coe,
    id_eq]
  simp only [Basis.coe_dualBasis]

/-- The coaction on polynomial functions is the algebra homomorphism `polynomialCoact`. -/
theorem polynomial_coact (b : Basis ι R V) :
    letI := polynomial H b
    coact (R := R) (C := H) (M := MvPolynomial ι R) = (polynomialCoact H b).toLinearMap := by
  have := Module.Finite.of_basis b
  have := Module.Projective.of_basis b
  let _ := dual R H V
  let _ := symmetricAlgebra R H (Module.Dual R V)
  let e := SymmetricAlgebra.equivMvPolynomial b.dualBasis
  -- The transported coaction is a composite of algebra homomorphisms.
  let φ : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⊗[R] H :=
    (Algebra.TensorProduct.map e.toAlgHom (AlgHom.id R H)).comp
      ((symmetricAlgebraCoact R H (Module.Dual R V)).comp e.symm.toAlgHom)
  have hφ : (letI := polynomial H b; coact (R := R) (C := H) (M := MvPolynomial ι R)) =
      φ.toLinearMap := by
    refine LinearMap.ext fun f ↦ ?_
    rw [polynomial, transport_coact_apply, ← LinearMap.rTensor_def,
      ← AlgEquiv.toAlgHom_toLinearMap, AlgHom.rTensor_toLinearMap_apply,
      ← AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_apply, symmetricAlgebra_coact]
    simp only [φ, e, AlgHom.toLinearMap_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  have h : φ = polynomialCoact H b := MvPolynomial.algHom_ext fun i ↦ by
    rw [polynomialCoact_X, ← polynomial_coact_X b i, hφ, AlgHom.toLinearMap_apply]
  exact hφ.trans (by rw [h])

theorem polynomial_coact_apply (b : Basis ι R V) (f : MvPolynomial ι R) :
    letI := polynomial H b
    coact (R := R) (C := H) f = polynomialCoact H b f := by
  rw [polynomial_coact, AlgHom.toLinearMap_apply]

variable (H) in
/-- The homogeneous polynomial functions of degree `d` on `V`, as a subcomodule of
`polynomial H b`: the image of the `d`-th symmetric power of `V*`. -/
noncomputable def polynomialHomogeneousSubcomodule (b : Basis ι R V) (d : ℕ) :
    letI := polynomial H b
    Subcomodule R H (MvPolynomial ι R) :=
  letI := polynomial H b
  haveI := Module.Finite.of_basis b
  haveI := Module.Projective.of_basis b
  letI := dual R H V
  letI := symmetricAlgebra R H (Module.Dual R V)
  (symmetricPowerSubcomodule R H (Module.Dual R V) d).map
    (transportToHom (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearEquiv)

@[simp]
theorem mem_polynomialHomogeneousSubcomodule (b : Basis ι R V) {d : ℕ} {f : MvPolynomial ι R} :
    f ∈ polynomialHomogeneousSubcomodule H b d ↔ f.IsHomogeneous d := by
  let _ := polynomial H b
  have := Module.Finite.of_basis b
  have := Module.Projective.of_basis b
  let _ := dual R H V
  let _ := symmetricAlgebra R H (Module.Dual R V)
  rw [polynomialHomogeneousSubcomodule, ← Subcomodule.mem_toSubmodule,
    Subcomodule.map_toSubmodule, transportToHom_toLinearMap, AlgEquiv.toLinearEquiv_toLinearMap,
    symmetricPowerSubcomodule_toSubmodule,
    SymmetricAlgebra.map_homogeneousSubmodule_equivMvPolynomial,
    MvPolynomial.mem_homogeneousSubmodule]

section Points

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- **Points act on polynomial functions by the contragredient substitution.** Under
`A ⊗[R] R[X] ≃ A[X]`, an `A`-point `g` substitutes `∑ j, g(S(c(b*ᵢ, b j))) X j` for `X i`; that
is, `(g • f)(v) = f(g⁻¹ v)`. -/
theorem algebraTensorAlgEquiv_endOfPoint_polynomial (b : Basis ι R V) (g : H →ₐ[R] A)
    (f : MvPolynomial ι R) :
    letI := polynomial H b
    MvPolynomial.algebraTensorAlgEquiv R A (endOfPoint (MvPolynomial ι R) g (1 ⊗ₜ f)) =
      MvPolynomial.aeval (fun i ↦ ∑ j, MvPolynomial.C
        (g (HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j)))) *
          MvPolynomial.X j) f := by
  let _ := polynomial H b
  -- Both sides are algebra homomorphisms in `f`, so it suffices to compare them on `X i`.
  let Ψ : MvPolynomial ι R →ₐ[R] MvPolynomial ι A :=
    ((MvPolynomial.algebraTensorAlgEquiv R A).toAlgHom.restrictScalars R).comp
      ((Algebra.TensorProduct.comm R (MvPolynomial ι R) A).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id R _) g).comp (polynomialCoact H b)))
  have hΨ (f : MvPolynomial ι R) :
      MvPolynomial.algebraTensorAlgEquiv R A (endOfPoint (MvPolynomial ι R) g (1 ⊗ₜ f)) =
        Ψ f := by
    rw [endOfPoint_tmul, one_smul, polynomial_coact_apply]
    simp only [Ψ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_restrictScalars']
    rw [AlgHom.lTensor_toLinearMap_apply, ← Algebra.TensorProduct.comm_toLinearEquiv,
      AlgEquiv.toLinearEquiv_apply]
  rw [hΨ]
  congr 1
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [Ψ, Algebra.TensorProduct.map_tmul, MvPolynomial.smul_eq_C_mul]

end Points

/-! ### Binary forms with binomial support -/

section Binomial

/-- The monomial `xⁱ yʲ` lies in the span of the monomials of degree `d` with nonzero binomial
coefficient exactly when `i + j = d` and `d choose i` is nonzero. -/
private theorem X_pow_mul_X_pow_mem_restrictSupport_iff [Nontrivial R] {d i j : ℕ} :
    (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j : MvPolynomial (Fin 2) R) ∈
        MvPolynomial.restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0} ↔
      i + j = d ∧ (d.choose i : R) ≠ 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mem_restrictSupport]
  simp

variable [NoZeroDivisors R]

/-- The coaction sends a monomial `xⁱ yʲ` with nonzero `(i + j) choose i` into the tensor
product of the binomial span with `H`. -/
private theorem polynomialCoact_X_pow_mul_X_pow_mem (b : Basis (Fin 2) R V) {d i j : ℕ}
    (hij : i + j = d) (hi : (d.choose i : R) ≠ 0) :
    polynomialCoact H b (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j) ∈
      LinearMap.range (TensorProduct.map
        (MvPolynomial.restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0}).subtype
        (LinearMap.id : H →ₗ[R] H)) := by
  have : Nontrivial R := ⟨⟨_, _, hi⟩⟩
  set c : Fin 2 → Fin 2 → H := fun i j ↦
    HopfAlgebra.antipode R (matrixCoefficient (C := H) (b.coord i) (b j))
  -- Expand both powers by the binomial theorem; the double sum has one term for each pair of
  -- powers of `x` taken from the two factors.
  rw [map_mul, map_pow, map_pow, polynomialCoact_X, polynomialCoact_X, Fin.sum_univ_two,
    Fin.sum_univ_two, add_pow, add_pow, Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun r hr ↦ Submodule.sum_mem _ fun s hs ↦ ?_
  have hr' : r ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hs' : s ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hterm : (MvPolynomial.X 0 ⊗ₜ[R] c 0 0) ^ r * (MvPolynomial.X 1 ⊗ₜ[R] c 0 1) ^ (i - r) *
        (i.choose r : MvPolynomial (Fin 2) R ⊗[R] H) *
      ((MvPolynomial.X 0 ⊗ₜ[R] c 1 0) ^ s * (MvPolynomial.X 1 ⊗ₜ[R] c 1 1) ^ (j - s) *
        (j.choose s : MvPolynomial (Fin 2) R ⊗[R] H)) =
      ((i.choose r * j.choose s : ℕ) : R) •
        ((MvPolynomial.X 0 ^ (r + s) * MvPolynomial.X 1 ^ (i - r + (j - s)) :
          MvPolynomial (Fin 2) R) ⊗ₜ[R]
          (c 0 0 ^ r * c 0 1 ^ (i - r) * (c 1 0 ^ s * c 1 1 ^ (j - s)))) := by
    simp only [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
      ← nsmul_eq_mul', smul_mul_assoc, mul_smul_comm, smul_smul, Nat.cast_smul_eq_nsmul]
    rw [Nat.mul_comm]
    congr 2
    ring
  rw [hterm]
  by_cases h0 : ((i.choose r * j.choose s : ℕ) : R) = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  refine Submodule.smul_mem _ _ ⟨⟨_, ?_⟩ ⊗ₜ[R] _, rfl⟩
  -- The monomial `x^(r + s) y^(d - r - s)` has nonzero binomial coefficient, by the
  -- factorization of `C(d, i) C(i, r) C(j, s)` through `C(d, r + s)`.
  refine (X_pow_mul_X_pow_mem_restrictSupport_iff (R := R)).mpr ⟨by omega, fun hrs ↦ ?_⟩
  have key := congrArg (Nat.cast : ℕ → R) (Nat.add_choose_mul_choose_mul_choose hr' hs')
  rw [hij] at key
  push_cast at key h0
  rw [hrs, zero_mul, zero_mul, mul_assoc, mul_eq_zero] at key
  exact key.elim hi h0

variable (H) in
/-- **The binomial span of binary forms**, as a subcomodule of the polynomial functions on a
comodule with a basis indexed by `Fin 2`, over a ring without zero divisors: the span of the
monomials `xⁱ yʲ` in `x = X 0` and `y = X 1` of degree `i + j = d` whose binomial coefficient
`d choose i` is nonzero in `R`.

For the standard representation of `SL₂` over a field this is the simple socle of the binary forms
of degree `d`. -/
noncomputable def polynomialBinomialSubcomodule (b : Basis (Fin 2) R V) (d : ℕ) :
    letI := polynomial H b
    Subcomodule R H (MvPolynomial (Fin 2) R) :=
  letI := polynomial H b
  Subcomodule.ofSubmodule
    (MvPolynomial.restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0}) <| by
    -- It suffices to check the spanning monomials.
    suffices h : MvPolynomial.restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0} ≤
        (LinearMap.range (TensorProduct.map (MvPolynomial.restrictSupport R
          {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0}).subtype
            (LinearMap.id : H →ₗ[R] H))).comap (polynomialCoact H b).toLinearMap by
      intro f hf
      rw [polynomial_coact]
      exact h hf
    refine (MvPolynomial.restrictSupport_eq_span R _).trans_le (Submodule.span_le.mpr ?_)
    rintro _ ⟨m, ⟨hm, hmd⟩, rfl⟩
    beta_reduce
    rw [SetLike.mem_coe, Submodule.mem_comap, AlgHom.toLinearMap_apply,
      MvPolynomial.monomial_fin_two, map_one, one_mul]
    exact polynomialCoact_X_pow_mul_X_pow_mem b hm hmd

/-- The underlying submodule of the binomial span is spanned by its monomials. -/
@[simp]
theorem polynomialBinomialSubcomodule_toSubmodule (b : Basis (Fin 2) R V) (d : ℕ) :
    letI := polynomial H b
    (polynomialBinomialSubcomodule H b d).toSubmodule =
      MvPolynomial.restrictSupport R {m | m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0} :=
  (rfl)

/-- A polynomial lies in the binomial span exactly when each of its monomials `xⁱ yʲ` has degree
`i + j = d` and nonzero binomial coefficient `d choose i`. -/
@[simp]
theorem mem_polynomialBinomialSubcomodule (b : Basis (Fin 2) R V) {d : ℕ}
    {f : MvPolynomial (Fin 2) R} :
    f ∈ polynomialBinomialSubcomodule H b d ↔
      ∀ m ∈ f.support, m 0 + m 1 = d ∧ (d.choose (m 0) : R) ≠ 0 :=
  Iff.rfl

/-- The monomial `xⁱ yʲ` lies in the binomial span of degree `d` exactly when `i + j = d` and
`d choose i` is nonzero. -/
theorem X_pow_mul_X_pow_mem_polynomialBinomialSubcomodule_iff [Nontrivial R]
    (b : Basis (Fin 2) R V) {d i j : ℕ} :
    (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j : MvPolynomial (Fin 2) R) ∈
        polynomialBinomialSubcomodule H b d ↔ i + j = d ∧ (d.choose i : R) ≠ 0 :=
  X_pow_mul_X_pow_mem_restrictSupport_iff

/-- The binomial span consists of homogeneous polynomials of degree `d`. -/
theorem polynomialBinomialSubcomodule_le_polynomialHomogeneousSubcomodule
    (b : Basis (Fin 2) R V) (d : ℕ) :
    polynomialBinomialSubcomodule H b d ≤ polynomialHomogeneousSubcomodule H b d := by
  intro f hf
  rw [mem_polynomialHomogeneousSubcomodule]
  intro m hm
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  simpa using
    ((mem_polynomialBinomialSubcomodule b).mp hf m (MvPolynomial.mem_support_iff.mpr hm)).1

end Binomial

end Comodule

end TauCeti
