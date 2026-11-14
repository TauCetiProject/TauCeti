/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The algebraic de Rham complex of a commutative algebra

For an algebra `S` over a commutative ring `R`, the exterior algebra `ExteriorAlgebra S Ω[S⁄R]` of
its module of Kähler differentials carries a unique `R`-linear exterior differential `extDeriv R S`
extending `KaehlerDifferential.D R S` in degree zero, annihilating exact `1`-forms `D R S s`, and
satisfying the graded Leibniz rule

`extDeriv R S (x * y) = extDeriv R S x * y + involute x * extDeriv R S y`.

Equipped with the cohomological `ℤ`-grading `grading R S` obtained by restricting scalars from
`TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R]` to `R`, this makes `ExteriorAlgebra S Ω[S⁄R]` a
differential graded `R`-algebra (`isDGAlgebra R S`), valid in arbitrary characteristic without
smoothness or finiteness assumptions on `R → S`.

We prove the universal property (`liftDGAlgHom`, `dgAlgHom_ext`) of the algebraic de Rham complex
among differential graded `R`-algebras whose degree-one elements square to zero, establish
covariant functoriality (`map`) along `R`-algebra homomorphisms compatible with
`KaehlerDifferential.mapSemilinear`, and derive explicit coordinate formulas over multivariate
polynomial rings `MvPolynomial σ R` (for arbitrary, possibly infinite variable sets `σ`).

## Main definitions

* `TauCeti.KaehlerDeRham.grading R S`: the `ℤ`-grading of `ExteriorAlgebra S Ω[S⁄R]` as an
  `R`-algebra, obtained by restricting scalars from `TauCeti.ExteriorAlgebra.integerGrading`.
* `TauCeti.KaehlerDeRham.extDeriv R S`: the algebraic exterior derivative on
  `ExteriorAlgebra S Ω[S⁄R]`, as an `R`-linear endomorphism.
* `TauCeti.KaehlerDeRham.liftDGAlgHom`: universal property lifting an `R`-algebra homomorphism
  `S →ₐ[R] B` into the degree-zero center of a DG `R`-algebra with square-zero degree-one piece to a
  morphism of DG `R`-algebras out of `ExteriorAlgebra S Ω[S⁄R]`.
* `TauCeti.KaehlerDeRham.map`: functoriality of the algebraic de Rham DG algebra along an
  `R`-algebra homomorphism `A →ₐ[R] B`.

## Main results

* `TauCeti.KaehlerDeRham.extDeriv_mul`, `extDeriv_mul_of_mem_exteriorPower`,
  `extDeriv_mul_of_mem_grading`: the graded Leibniz rule for `extDeriv R S`.
* `TauCeti.KaehlerDeRham.extDeriv_extDeriv`: `extDeriv R S` squares to zero.
* `TauCeti.KaehlerDeRham.isDGAlgebra`: `ExteriorAlgebra S Ω[S⁄R]` is a differential graded
  `R`-algebra under `grading R S` and `extDeriv R S`.
* `TauCeti.KaehlerDeRham.extDeriv_unique`, `isDGAlgebra_extDeriv_unique`: uniqueness of the
  algebraic exterior derivative.
* `TauCeti.KaehlerDeRham.dgAlgHom_ext`, `dgAlgHom_ext_iff`: two DG algebra morphisms out of
  `ExteriorAlgebra S Ω[S⁄R]` agree if and only if they agree on `S`.
* `TauCeti.KaehlerDeRham.extDeriv_algebraMap_mvPolynomial_eq_sum_vars`: coordinate formula
  `d p = ∑ i ∈ p.vars, pderiv i p • ι (D (X i))` over `MvPolynomial σ R` for arbitrary `σ`.

## Implementation notes

To avoid division by `2` or basis hypotheses, `extDeriv R S` is constructed in two steps:

1. Using Mathlib's presentation `KaehlerDifferential.quotKerTotalEquiv` of `Ω[S⁄R]` as the quotient
   of `S →₀ S` by `KaehlerDifferential.kerTotal R S`, the map `single x c ↦ ι (D c) * ι (D x)`
   factors to an `R`-linear map `Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R]` taking values in
   `⋀[S]^2 Ω[S⁄R]`, vanishing on `D x`, and satisfying `d₁ (s • ω) = ι (D s) * ι ω + s • d₁ ω`.
2. On a private type `OddDual R S` with carrier `A × A` (`A = ExteriorAlgebra S Ω[S⁄R]`) and graded
   square-zero multiplication `(a, a') * (b, b') = (a * b, a' * b + involute a * b')`, the ring map
   `s ↦ (algebraMap s, ι (D s))` lands in the center because `ι m * b = involute b * ι m`. This
   gives `OddDual R S` an `S`-algebra structure without creating an `SMul S` diamond, and
   `ω ↦ (ι ω, d₁ ω)` is `S`-linear and squares to zero. Applying `ExteriorAlgebra.lift` yields an
   `S`-algebra homomorphism whose first component is the identity and whose second component is
   `extDeriv R S`.

## References

* A. Grothendieck, *On the de Rham cohomology of algebraic varieties*, Publ. Math. IHÉS **29**
  (1966), 95–103.
* N. Bourbaki, *Algebra*, Chapter III, §10.
-/

public section

open CliffordAlgebra

namespace TauCeti.KaehlerDeRham

section Grading

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- The cohomological `ℤ`-grading of the algebraic de Rham algebra `ExteriorAlgebra S Ω[S⁄R]` over
`R`, obtained by restricting scalars from `TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R]`. -/
noncomputable def grading (p : ℤ) : Submodule R (ExteriorAlgebra S Ω[S⁄R]) :=
  (TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R] p).restrictScalars R

/-- The algebraic de Rham algebra is internally `ℤ`-graded as an `R`-algebra. -/
noncomputable instance gradedAlgebra : GradedAlgebra (grading R S) :=
  inferInstanceAs <|
    GradedAlgebra fun p ↦ (TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R] p).restrictScalars R

variable {R S}

/-- Membership in `grading R S p` agrees with membership in the `S`-linear integer grading. -/
@[simp]
theorem mem_grading_iff {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} :
    x ∈ grading R S p ↔ x ∈ TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R] p :=
  (Iff.rfl)

/-- In nonnegative degree `n`, `grading R S n` is the `n`-th exterior power `⋀[S]^n Ω[S⁄R]`. -/
theorem mem_grading_natCast {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]} :
    x ∈ grading R S n ↔ x ∈ ⋀[S]^n Ω[S⁄R] := by
  simp

/-- The grading of `ExteriorAlgebra S Ω[S⁄R]` vanishes in negative degrees. -/
theorem grading_of_neg {p : ℤ} (hp : p < 0) : grading R S p = ⊥ := by
  ext x
  simp [TauCeti.ExteriorAlgebra.integerGrading_of_neg hp]

/-- Elements of `S` sit in degree zero of the algebraic de Rham grading. -/
theorem algebraMap_mem_grading_zero (s : S) :
    algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s ∈ grading R S 0 := by
  rw [← Nat.cast_zero, mem_grading_natCast, _root_.ExteriorAlgebra.exteriorPower, pow_zero]
  exact Submodule.algebraMap_mem s

/-- Kähler `1`-forms sit in degree one of the algebraic de Rham grading. -/
theorem ι_mem_grading_one (ω : Ω[S⁄R]) :
    ExteriorAlgebra.ι S ω ∈ grading R S 1 :=
  (mem_grading_iff).mpr (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one ω)

end Grading

/-! ### Construction of the exterior derivative -/

section Construction

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Auxiliary `R`-linear map `(S →₀ S) →ₗ[R] ExteriorAlgebra S Ω[S⁄R]` sending `single x c` to
`ι (D c) * ι (D x)`. -/
private noncomputable def preExtDerivOne : (S →₀ S) →ₗ[R] ExteriorAlgebra S Ω[S⁄R] :=
  Finsupp.lsum R fun x : S ↦
    (LinearMap.mulRight R (ExteriorAlgebra.ι S (KaehlerDifferential.D R S x))).comp
      (((ExteriorAlgebra.ι S).restrictScalars R).comp (KaehlerDifferential.D R S).toLinearMap)

private theorem preExtDerivOne_single (x c : S) :
    preExtDerivOne R S (Finsupp.single x c) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S c) *
        ExteriorAlgebra.ι S (KaehlerDifferential.D R S x) := by
  simp [preExtDerivOne]

private theorem preExtDerivOne_smul (s : S) (v : S →₀ S) :
    preExtDerivOne R S (s • v) =
      s • preExtDerivOne R S v +
        ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) *
          ExteriorAlgebra.ι S (Finsupp.linearCombination S (KaehlerDifferential.D R S) v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ ih₁ ih₂ =>
    rw [smul_add, map_add, map_add, map_add, map_add, smul_add, mul_add, ih₁, ih₂]
    abel
  | single x c =>
    rw [Finsupp.smul_single, smul_eq_mul, preExtDerivOne_single, preExtDerivOne_single,
      Finsupp.linearCombination_single, Derivation.leibniz, map_add, map_smul, map_smul, map_smul,
      add_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]

private theorem preExtDerivOne_eq_zero_of_mem_kerTotal {v : S →₀ S}
    (hv : v ∈ KaehlerDifferential.kerTotal R S) : preExtDerivOne R S v = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨r, rfl⟩
    · simp [preExtDerivOne_single]
    · simp only [map_sub, map_add, preExtDerivOne_single, Derivation.map_one_eq_zero, map_zero,
        zero_mul, sub_zero]
      exact ExteriorAlgebra.ι_add_mul_swap _ _
    · simp [preExtDerivOne_single]
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, ih₁, ih₂, add_zero]
  | smul s v hv ih =>
    have hker : Finsupp.linearCombination S (KaehlerDifferential.D R S) v = 0 := by
      rwa [← LinearMap.mem_ker, KaehlerDifferential.kerTotal_eq]
    rw [preExtDerivOne_smul, ih, hker, smul_zero, map_zero, mul_zero, add_zero]

/-- Auxiliary degree-one exterior derivative `Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R]`. -/
private noncomputable def extDerivOne : Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R] :=
  (((KaehlerDifferential.kerTotal R S).restrictScalars R).liftQ (preExtDerivOne R S)
    fun v hv ↦ preExtDerivOne_eq_zero_of_mem_kerTotal R S
      ((Submodule.restrictScalars_mem R _ v).mp hv)).comp
    ((Submodule.Quotient.restrictScalarsEquiv R
        (KaehlerDifferential.kerTotal R S)).symm.toLinearMap.comp
      ((KaehlerDifferential.quotKerTotalEquiv R S).symm.toLinearMap.restrictScalars R))

private theorem extDerivOne_linearCombination (w : S →₀ S) :
    extDerivOne R S (Finsupp.linearCombination S (KaehlerDifferential.D R S) w) =
      preExtDerivOne R S w := by
  have hw : (KaehlerDifferential.quotKerTotalEquiv R S).symm
      (Finsupp.linearCombination S (KaehlerDifferential.D R S) w) =
      Submodule.Quotient.mk w := by
    apply (KaehlerDifferential.quotKerTotalEquiv R S).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  simp only [extDerivOne, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_toLinearMap, hw, Submodule.Quotient.restrictScalarsEquiv_symm_mk]
  exact Submodule.liftQ_apply _ _ w

private theorem extDerivOne_D (x : S) :
    extDerivOne R S (KaehlerDifferential.D R S x) = 0 := by
  rw [← one_smul S (KaehlerDifferential.D R S x), ← Finsupp.linearCombination_single,
    extDerivOne_linearCombination, preExtDerivOne_single, Derivation.map_one_eq_zero, map_zero,
    zero_mul]

private theorem extDerivOne_smul (s : S) (ω : Ω[S⁄R]) :
    extDerivOne R S (s • ω) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) * ExteriorAlgebra.ι S ω +
        s • extDerivOne R S ω := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R S ω
  rw [← LinearMap.map_smul, extDerivOne_linearCombination, extDerivOne_linearCombination,
    preExtDerivOne_smul, add_comm]

private theorem extDerivOne_mem_exteriorPower_two (ω : Ω[S⁄R]) :
    extDerivOne R S ω ∈ ⋀[S]^2 Ω[S⁄R] := by
  induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
      ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
      Submodule.span_induction with
  | mem _ hω =>
    obtain ⟨x, rfl⟩ := hω
    rw [extDerivOne_D]
    exact zero_mem _
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add _ _ _ _ ih₁ ih₂ =>
    rw [map_add]
    exact add_mem ih₁ ih₂
  | smul s ω _ ih =>
    rw [extDerivOne_smul]
    exact add_mem
      (SetLike.mul_mem_graded (ExteriorAlgebra.ι_mem_exteriorPower_one _)
        (ExteriorAlgebra.ι_mem_exteriorPower_one _))
      (Submodule.smul_mem _ s ih)

/-- Auxiliary odd dual-number algebra over `S` with carrier `A × A` and multiplication
`(a, a') * (b, b') = (a * b, a' * b + involute a * b')`. -/
@[ext]
private structure OddDual where
  fst : ExteriorAlgebra S Ω[S⁄R]
  snd : ExteriorAlgebra S Ω[S⁄R]

private noncomputable instance : Zero (OddDual R S) := ⟨⟨0, 0⟩⟩
private noncomputable instance : One (OddDual R S) := ⟨⟨1, 0⟩⟩
private noncomputable instance : Add (OddDual R S) := ⟨fun x y ↦ ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private noncomputable instance : Neg (OddDual R S) := ⟨fun x ↦ ⟨-x.fst, -x.snd⟩⟩
private noncomputable instance : Sub (OddDual R S) := ⟨fun x y ↦ ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private noncomputable instance : SMul ℕ (OddDual R S) := ⟨fun n x ↦ ⟨n • x.fst, n • x.snd⟩⟩
private noncomputable instance : SMul ℤ (OddDual R S) := ⟨fun z x ↦ ⟨z • x.fst, z • x.snd⟩⟩

private noncomputable instance : Mul (OddDual R S) :=
  ⟨fun x y ↦ ⟨x.fst * y.fst,
    x.snd * y.fst + involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x.fst * y.snd⟩⟩

@[simp] private theorem OddDual.zero_fst : (0 : OddDual R S).fst = 0 := rfl
@[simp] private theorem OddDual.zero_snd : (0 : OddDual R S).snd = 0 := rfl
@[simp] private theorem OddDual.one_fst : (1 : OddDual R S).fst = 1 := rfl
@[simp] private theorem OddDual.one_snd : (1 : OddDual R S).snd = 0 := rfl
@[simp] private theorem OddDual.add_fst (x y : OddDual R S) : (x + y).fst = x.fst + y.fst := rfl
@[simp] private theorem OddDual.add_snd (x y : OddDual R S) : (x + y).snd = x.snd + y.snd := rfl
@[simp] private theorem OddDual.neg_fst (x : OddDual R S) : (-x).fst = -x.fst := rfl
@[simp] private theorem OddDual.neg_snd (x : OddDual R S) : (-x).snd = -x.snd := rfl
@[simp] private theorem OddDual.sub_fst (x y : OddDual R S) : (x - y).fst = x.fst - y.fst := rfl
@[simp] private theorem OddDual.sub_snd (x y : OddDual R S) : (x - y).snd = x.snd - y.snd := rfl
@[simp] private theorem OddDual.nsmul_fst (n : ℕ) (x : OddDual R S) : (n • x).fst = n • x.fst := rfl
@[simp] private theorem OddDual.nsmul_snd (n : ℕ) (x : OddDual R S) : (n • x).snd = n • x.snd := rfl
@[simp] private theorem OddDual.zsmul_fst (z : ℤ) (x : OddDual R S) : (z • x).fst = z • x.fst := rfl
@[simp] private theorem OddDual.zsmul_snd (z : ℤ) (x : OddDual R S) : (z • x).snd = z • x.snd := rfl
@[simp] private theorem OddDual.mul_fst (x y : OddDual R S) : (x * y).fst = x.fst * y.fst := rfl
@[simp] private theorem OddDual.mul_snd (x y : OddDual R S) :
    (x * y).snd = x.snd * y.fst + involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x.fst * y.snd := rfl

private noncomputable instance : Ring (OddDual R S) where
  add_assoc x y z := by ext <;> exact add_assoc _ _ _
  zero_add x := by ext <;> exact zero_add _
  add_zero x := by ext <;> exact add_zero _
  nsmul n x := n • x
  nsmul_zero x := by ext <;> exact zero_smul ℕ _
  nsmul_succ n x := by ext <;> exact succ_nsmul _ n
  zsmul z x := z • x
  zsmul_zero' x := by ext <;> exact zero_smul ℤ _
  zsmul_succ' n x := by ext <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n x := by ext <;> exact SubNegMonoid.zsmul_neg' n _
  neg_add_cancel x := by ext <;> exact neg_add_cancel _
  add_comm x y := by ext <;> exact add_comm _ _
  sub_eq_add_neg x y := by ext <;> exact sub_eq_add_neg _ _
  left_distrib x y z := by ext <;> simp only [OddDual.mul_fst, OddDual.mul_snd, OddDual.add_fst,
    OddDual.add_snd, mul_add]; abel
  right_distrib x y z := by ext <;> simp only [OddDual.mul_fst, OddDual.mul_snd, OddDual.add_fst,
    OddDual.add_snd, map_add, add_mul]; abel
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  mul_assoc x y z := by ext <;> simp only [OddDual.mul_fst, OddDual.mul_snd, map_mul, add_mul,
    mul_add, mul_assoc]; abel
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

private noncomputable def oddDualRingHom : S →+* OddDual R S where
  toFun s := ⟨algebraMap S _ s, ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)⟩
  map_one' := by ext <;> simp
  map_mul' s t := by
    ext
    · exact map_mul _ s t
    · simp only [OddDual.mul_snd, Derivation.leibniz, map_add, map_smul, AlgHom.commutes]
      rw [← Algebra.commutes t, ← Algebra.smul_def, ← Algebra.smul_def, add_comm]
  map_zero' := by ext <;> simp
  map_add' s t := by ext <;> simp

private noncomputable instance : Algebra S (OddDual R S) :=
  (oddDualRingHom R S).toAlgebra' fun s z ↦ by
    ext
    · exact Algebra.commutes s z.fst
    · simp only [OddDual.mul_snd, oddDualRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [ExteriorAlgebra.ι_mul_eq_involute_mul, AlgHom.commutes, Algebra.commutes s z.snd,
        add_comm]

@[simp] private theorem OddDual.algebraMap_fst (s : S) :
    (algebraMap S (OddDual R S) s).fst = algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s := rfl
@[simp] private theorem OddDual.algebraMap_snd (s : S) :
    (algebraMap S (OddDual R S) s).snd = ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) := rfl
@[simp] private theorem OddDual.smul_fst (s : S) (z : OddDual R S) :
    (s • z).fst = algebraMap S _ s * z.fst := rfl
@[simp] private theorem OddDual.smul_snd (s : S) (z : OddDual R S) :
    (s • z).snd =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) * z.fst +
        involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (algebraMap S _ s) * z.snd := rfl

private noncomputable def oddDualGenerator : Ω[S⁄R] →ₗ[S] OddDual R S where
  toFun ω := ⟨ExteriorAlgebra.ι S ω, extDerivOne R S ω⟩
  map_add' ω₁ ω₂ := by ext <;> exact map_add _ ω₁ ω₂
  map_smul' s ω := by
    ext
    · simp [Algebra.smul_def]
    · simp [extDerivOne_smul, AlgHom.commutes, Algebra.smul_def]

@[simp] private theorem oddDualGenerator_fst (ω : Ω[S⁄R]) :
    (oddDualGenerator R S ω).fst = ExteriorAlgebra.ι S ω := rfl
@[simp] private theorem oddDualGenerator_snd (ω : Ω[S⁄R]) :
    (oddDualGenerator R S ω).snd = extDerivOne R S ω := rfl

private theorem oddDualGenerator_sq_zero (ω : Ω[S⁄R]) :
    oddDualGenerator R S ω * oddDualGenerator R S ω = 0 := by
  ext
  · exact ExteriorAlgebra.ι_sq_zero ω
  · simp only [OddDual.mul_snd, OddDual.zero_snd, oddDualGenerator_fst, oddDualGenerator_snd]
    have hinv : involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (extDerivOne R S ω) =
        extDerivOne R S ω := by
      rw [TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower
        (extDerivOne_mem_exteriorPower_two R S ω)]
      simp
    rw [involute_ι, neg_mul, ExteriorAlgebra.ι_mul_eq_involute_mul, hinv, add_neg_cancel]

private noncomputable def oddDualLift : ExteriorAlgebra S Ω[S⁄R] →ₐ[S] OddDual R S :=
  ExteriorAlgebra.lift S ⟨oddDualGenerator R S, oddDualGenerator_sq_zero R S⟩

private noncomputable def oddDualFstAlgHom : OddDual R S →ₐ[S] ExteriorAlgebra S Ω[S⁄R] where
  toFun := OddDual.fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem oddDualLift_fst (x : ExteriorAlgebra S Ω[S⁄R]) :
    (oddDualLift R S x).fst = x := by
  have h : (oddDualFstAlgHom R S).comp (oddDualLift R S) = AlgHom.id S _ :=
    ExteriorAlgebra.hom_ext <| LinearMap.ext fun ω ↦ by
      simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        oddDualLift, ExteriorAlgebra.lift_ι_apply, AlgHom.id_apply]
      rfl
  exact AlgHom.congr_fun h x

/-- **The algebraic exterior derivative** on the algebraic de Rham algebra
`ExteriorAlgebra S Ω[S⁄R]`, extending `KaehlerDifferential.D R S` in degree zero and satisfying
`extDeriv R S (x * y) = extDeriv R S x * y + involute x * extDeriv R S y`. -/
noncomputable def extDeriv : ExteriorAlgebra S Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R] where
  toFun x := (oddDualLift R S x).snd
  map_add' x y := congrArg OddDual.snd (map_add (oddDualLift R S) x y)
  map_smul' r x := by
    rw [← IsScalarTower.algebraMap_smul S r x, AlgHom.map_smul_of_tower, OddDual.smul_snd,
      Derivation.map_algebraMap, map_zero, zero_mul, zero_add, AlgHom.commutes,
      ← Algebra.smul_def, IsScalarTower.algebraMap_smul, RingHom.id_apply]

variable {R S}

private theorem extDeriv_apply (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S x = (oddDualLift R S x).snd := rfl

private theorem extDeriv_ι_eq_extDerivOne (ω : Ω[S⁄R]) :
    extDeriv R S (ExteriorAlgebra.ι S ω) = extDerivOne R S ω := by
  rw [extDeriv_apply, oddDualLift, ExteriorAlgebra.lift_ι_apply, oddDualGenerator_snd]

/-- On degree-zero elements `algebraMap S _ s`, the exterior derivative is the universal Kähler
differential `ι (D R S s)`. -/
@[simp]
theorem extDeriv_algebraMap (s : S) :
    extDeriv R S (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) := by
  rw [extDeriv_apply, AlgHom.commutes, OddDual.algebraMap_snd]

/-- The exterior derivative annihilates `1`. -/
@[simp]
theorem extDeriv_one : extDeriv R S 1 = 0 := by
  rw [← map_one (algebraMap S (ExteriorAlgebra S Ω[S⁄R])), extDeriv_algebraMap,
    Derivation.map_one_eq_zero, map_zero]

/-- The exterior derivative annihilates scalars from the base ring `R`. -/
@[simp]
theorem extDeriv_algebraMap_base (r : R) :
    extDeriv R S (algebraMap R (ExteriorAlgebra S Ω[S⁄R]) r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, extDeriv_one, smul_zero]

/-- Exact `1`-forms `ι (D R S s)` are closed under the exterior derivative. -/
@[simp]
theorem extDeriv_ι_D (s : S) :
    extDeriv R S (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) = 0 := by
  rw [extDeriv_ι_eq_extDerivOne, extDerivOne_D]

/-- **The graded Leibniz rule** for `extDeriv R S`, expressed uniformly via the grade involution. -/
theorem extDeriv_mul (x y : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (x * y) =
      extDeriv R S x * y +
        involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x * extDeriv R S y := by
  rw [extDeriv_apply, map_mul, OddDual.mul_snd, oddDualLift_fst, oddDualLift_fst, ← extDeriv_apply,
    ← extDeriv_apply]

/-- Scalar multiplication by `s : S` satisfies the Leibniz rule
`extDeriv R S (s • x) = ι (D R S s) * x + s • extDeriv R S x`. -/
theorem extDeriv_smul (s : S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (s • x) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) * x + s • extDeriv R S x := by
  rw [Algebra.smul_def, extDeriv_mul, extDeriv_algebraMap, AlgHom.commutes, ← Algebra.smul_def]

/-- On a generating `1`-form `s • D R S t`, the exterior derivative is `ι (D s) * ι (D t)`. -/
theorem extDeriv_ι_smul_D (s t : S) :
    extDeriv R S (ExteriorAlgebra.ι S (s • KaehlerDifferential.D R S t)) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) *
        ExteriorAlgebra.ι S (KaehlerDifferential.D R S t) := by
  rw [LinearMap.map_smul, extDeriv_smul, extDeriv_ι_D, smul_zero, add_zero]

/-- The graded Leibniz rule for a left factor in the `n`-th exterior power `⋀[S]^n Ω[S⁄R]`. -/
theorem extDeriv_mul_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]}
    (hx : x ∈ ⋀[S]^n Ω[S⁄R]) (y : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (x * y) = extDeriv R S x * y + (-1 : S) ^ n • (x * extDeriv R S y) := by
  rw [extDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hx, smul_mul_assoc]

/-- The graded Leibniz rule for a homogeneous left factor of integer degree `p`. -/
theorem extDeriv_mul_of_mem_grading {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]}
    (hx : x ∈ grading R S p) (y : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (x * y) = extDeriv R S x * y + p.negOnePow • (x * extDeriv R S y) := by
  rw [extDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_integerGrading hx, smul_mul_assoc]

/-- `extDeriv R S` anticommutes with the grade involution on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem extDeriv_involute (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x) =
      -involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (extDeriv R S x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap s =>
    rw [AlgHom.commutes, extDeriv_algebraMap, involute_ι, neg_neg]
  | ι ω =>
    rw [involute_ι, map_neg, extDeriv_ι_eq_extDerivOne,
      TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower
        (extDerivOne_mem_exteriorPower_two R S ω)]
    simp
  | mul x y ihx ihy =>
    rw [map_mul, extDeriv_mul, ihx, ihy, involute_involute, extDeriv_mul, map_add, map_mul,
      map_mul, involute_involute, neg_mul, mul_neg]
    abel
  | add x y ihx ihy =>
    rw [map_add, map_add, ihx, ihy, map_add, map_add, neg_add_rev]
    abel

/-- **The exterior derivative squares to zero** in arbitrary characteristic. -/
@[simp]
theorem extDeriv_extDeriv (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (extDeriv R S x) = 0 := by
  have hmul : ∀ a b : ExteriorAlgebra S Ω[S⁄R],
      extDeriv R S (extDeriv R S (a * b)) =
        extDeriv R S (extDeriv R S a) * b + a * extDeriv R S (extDeriv R S b) := fun a b ↦ by
    rw [extDeriv_mul, map_add, extDeriv_mul, extDeriv_mul, extDeriv_involute, involute_involute,
      neg_mul]
    abel
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [extDeriv_algebraMap, extDeriv_ι_D]
  | ι ω =>
    induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
        ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
        Submodule.span_induction with
    | mem _ hω =>
      obtain ⟨s, rfl⟩ := hω
      rw [extDeriv_ι_D, map_zero]
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂, add_zero]
    | smul s ω _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def, hmul, extDeriv_algebraMap, extDeriv_ι_D, ih,
        zero_mul, mul_zero, add_zero]
  | mul x y ihx ihy => rw [hmul, ihx, ihy, zero_mul, mul_zero, add_zero]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy, add_zero]

/-- As an `R`-linear endomorphism, `extDeriv R S` composes with itself to zero. -/
@[simp]
theorem comp_extDeriv_self : (extDeriv R S).comp (extDeriv R S) = 0 :=
  LinearMap.ext extDeriv_extDeriv

/-- `extDeriv R S` carries `⋀[S]^n Ω[S⁄R]` into `⋀[S]^(n + 1) Ω[S⁄R]`. -/
theorem extDeriv_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]}
    (hx : x ∈ ⋀[S]^n Ω[S⁄R]) : extDeriv R S x ∈ ⋀[S]^(n + 1) Ω[S⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap s =>
    rw [zero_add, extDeriv_algebraMap]
    exact ExteriorAlgebra.ι_mem_exteriorPower_one _
  | add x y i _ _ ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    rw [extDeriv_mul, involute_ι, neg_mul]
    have h₁ : extDeriv R S (ExteriorAlgebra.ι S ω) * x ∈ ⋀[S]^(i + 1 + 1) Ω[S⁄R] := by
      have hi : i + 1 + 1 = 2 + i := by omega
      rw [extDeriv_ι_eq_extDerivOne, hi]
      exact SetLike.mul_mem_graded (extDerivOne_mem_exteriorPower_two R S ω) hx
    have h₂ : ExteriorAlgebra.ι S ω * extDeriv R S x ∈ ⋀[S]^(i + 1 + 1) Ω[S⁄R] := by
      have hi : i + 1 + 1 = 1 + (i + 1) := by omega
      rw [hi]
      exact SetLike.mul_mem_graded (ExteriorAlgebra.ι_mem_exteriorPower_one ω) ih
    exact add_mem h₁ (neg_mem h₂)

/-- `extDeriv R S` raises the integer degree in `grading R S` by one. -/
theorem extDeriv_mem_grading {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S p) :
    extDeriv R S x ∈ grading R S (p + 1) := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [grading_of_neg hp, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [mem_grading_natCast] at hx
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [hn, mem_grading_natCast]
    exact extDeriv_mem_exteriorPower hx

variable (R S) in
/-- **The algebraic de Rham complex is a differential graded `R`-algebra.** -/
theorem isDGAlgebra : TauCeti.IsDGAlgebra (grading R S) (extDeriv R S) where
  map_mem := extDeriv_mem_grading
  sq_zero := extDeriv_extDeriv
  leibniz := extDeriv_mul_of_mem_grading

/-- **Uniqueness of the algebraic exterior derivative**: any `R`-linear map on
`ExteriorAlgebra S Ω[S⁄R]` that extends `ι ∘ D R S` on `S`, satisfies `d (d s) = 0` on `S`, and
obeys the graded Leibniz rule equals `extDeriv R S`. -/
theorem extDeriv_unique {d : ExteriorAlgebra S Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R]}
    (h_alg : ∀ s : S,
      d (algebraMap S _ s) = ExteriorAlgebra.ι S (KaehlerDifferential.D R S s))
    (h_sq : ∀ s : S, d (d (algebraMap S _ s)) = 0)
    (h_mul : ∀ x y : ExteriorAlgebra S Ω[S⁄R],
      d (x * y) = d x * y + involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x * d y) :
    d = extDeriv R S := by
  ext x
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [h_alg, extDeriv_algebraMap]
  | ι ω =>
    induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
        ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
        Submodule.span_induction with
    | mem _ hω =>
      obtain ⟨s, rfl⟩ := hω
      rw [← h_alg s, h_sq s, h_alg s, extDeriv_ι_D]
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂]
    | smul s ω _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def, h_mul, extDeriv_mul, h_alg, extDeriv_algebraMap, ih]
  | mul x y ihx ihy => rw [h_mul, extDeriv_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- A differential making `(ExteriorAlgebra S Ω[S⁄R], grading R S)` a differential graded
`R`-algebra and extending `ι ∘ D R S` on `S` is necessarily `extDeriv R S`. -/
theorem isDGAlgebra_extDeriv_unique {d : ExteriorAlgebra S Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R]}
    (hd : TauCeti.IsDGAlgebra (grading R S) d)
    (h_alg : ∀ s : S,
      d (algebraMap S _ s) = ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) :
    d = extDeriv R S := by
  refine extDeriv_unique h_alg (fun s ↦ hd.sq_zero _) fun x y ↦ ?_
  induction x using DirectSum.Decomposition.inductionOn (grading R S) with
  | zero => simp
  | homogeneous x =>
    rw [hd.leibniz x.property y,
      TauCeti.ExteriorAlgebra.involute_of_mem_integerGrading x.property, smul_mul_assoc]
  | add x x' ihx ihx' =>
    rw [add_mul, map_add, ihx, ihx', map_add, map_add, add_mul, add_mul]
    abel

end Construction

/-! ### Universal property and functoriality -/

section UniversalProperty

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [Ring B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}

/-- **Extensionality of DG algebra morphisms out of the algebraic de Rham complex**: two DG algebra
morphisms out of `ExteriorAlgebra S Ω[S⁄R]` agree as soon as they agree on degree zero (`S`). -/
theorem dgAlgHom_ext {hB : TauCeti.IsDGAlgebra ℬ dB}
    {Φ Ψ : TauCeti.DGAlgHom (isDGAlgebra R S) hB}
    (h : ∀ s : S,
      Φ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
        Ψ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s)) :
    Φ = Ψ := by
  ext x
  induction x using CliffordAlgebra.induction with
  | algebraMap s => exact h s
  | ι ω =>
    induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
        ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
        Submodule.span_induction with
    | mem _ hω =>
      obtain ⟨s, rfl⟩ := hω
      rw [← extDeriv_algebraMap, ← Φ.map_d, ← Ψ.map_d, h s]
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, ih₁, ih₂]
    | smul s ω _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def, map_mul, map_mul, h s, ih]
  | mul x y ihx ihy => rw [map_mul, map_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- Two DG algebra morphisms out of `ExteriorAlgebra S Ω[S⁄R]` are equal if and only if they agree
on `S`. -/
theorem dgAlgHom_ext_iff {hB : TauCeti.IsDGAlgebra ℬ dB}
    {Φ Ψ : TauCeti.DGAlgHom (isDGAlgebra R S) hB} :
    Φ = Ψ ↔
      ∀ s : S,
        Φ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
          Ψ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) :=
  ⟨fun h s ↦ by rw [h], dgAlgHom_ext⟩

section LiftTower

variable [Algebra S B] [IsScalarTower R S B]

private noncomputable def liftDerivation (hB : TauCeti.IsDGAlgebra ℬ dB)
    (hf₀ : ∀ s : S, algebraMap S B s ∈ ℬ 0) : Derivation R S B where
  toLinearMap := dB.comp (IsScalarTower.toAlgHom R S B).toLinearMap
  map_one_eq_zero' := by simp [hB.map_one_eq_zero]
  leibniz' s t := by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply,
      map_mul, Algebra.smul_def]
    rw [hB.toIsNonUnitalDGAlgebra.leibniz_of_mem_zero (hf₀ s), Algebra.commutes t (dB _),
      add_comm]

private theorem liftKaehler_mem_one (hB : TauCeti.IsDGAlgebra ℬ dB)
    (hf₀ : ∀ s : S, algebraMap S B s ∈ ℬ 0) (ω : Ω[S⁄R]) :
    (liftDerivation hB hf₀).liftKaehlerDifferential ω ∈ ℬ 1 := by
  induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
      ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
      Submodule.span_induction with
  | mem _ hω =>
    obtain ⟨s, rfl⟩ := hω
    simpa [liftDerivation] using hB.map_mem (hf₀ s)
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ ih₁ ih₂ => rw [map_add]; exact add_mem ih₁ ih₂
  | smul s ω _ ih =>
    rw [LinearMap.map_smul, Algebra.smul_def]
    simpa using SetLike.mul_mem_graded (hf₀ s) ih

private noncomputable def liftAlgHomAux (hB : TauCeti.IsDGAlgebra ℬ dB)
    (hf₀ : ∀ s : S, algebraMap S B s ∈ ℬ 0) (hsq : ∀ b ∈ ℬ 1, b * b = 0) :
    ExteriorAlgebra S Ω[S⁄R] →ₐ[S] B :=
  ExteriorAlgebra.lift S
    ⟨(liftDerivation hB hf₀).liftKaehlerDifferential,
      fun ω ↦ hsq _ (liftKaehler_mem_one hB hf₀ ω)⟩

private theorem liftAlgHomAux_mem (hB : TauCeti.IsDGAlgebra ℬ dB)
    (hf₀ : ∀ s : S, algebraMap S B s ∈ ℬ 0) (hsq : ∀ b ∈ ℬ 1, b * b = 0)
    {i : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S i) :
    liftAlgHomAux hB hf₀ hsq x ∈ ℬ i := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [grading_of_neg hi, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    clear hi
    rw [mem_grading_natCast] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap s =>
      rw [Nat.cast_zero, AlgHom.commutes]
      exact hf₀ s
    | add x y k _ _ ihx ihy =>
      rw [map_add]
      exact add_mem ihx ihy
    | mem_mul m hm k x _ ih =>
      obtain ⟨ω, rfl⟩ := hm
      have hk : ((k + 1 : ℕ) : ℤ) = 1 + (k : ℤ) := by push_cast; ring
      rw [map_mul, hk, liftAlgHomAux, ExteriorAlgebra.lift_ι_apply]
      exact SetLike.mul_mem_graded (liftKaehler_mem_one hB hf₀ ω) ih

private theorem liftAlgHomAux_map_d (hB : TauCeti.IsDGAlgebra ℬ dB)
    (hf₀ : ∀ s : S, algebraMap S B s ∈ ℬ 0) (hsq : ∀ b ∈ ℬ 1, b * b = 0)
    (x : ExteriorAlgebra S Ω[S⁄R]) :
    dB (liftAlgHomAux hB hf₀ hsq x) = liftAlgHomAux hB hf₀ hsq (extDeriv R S x) := by
  have hFD (s : S) :
      liftAlgHomAux hB hf₀ hsq (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) =
        dB (algebraMap S B s) := by
    rw [liftAlgHomAux, ExteriorAlgebra.lift_ι_apply]
    exact (liftDerivation hB hf₀).liftKaehlerDifferential_comp_D s
  set F := liftAlgHomAux hB hf₀ hsq
  have hleib (z w : ExteriorAlgebra S Ω[S⁄R]) :
      dB (F z * F w) =
        dB (F z) * F w +
          F (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) z) * dB (F w) := by
    induction z using DirectSum.Decomposition.inductionOn (grading R S) with
    | zero => simp
    | homogeneous z =>
      rw [hB.leibniz (liftAlgHomAux_mem hB hf₀ hsq z.property),
        TauCeti.ExteriorAlgebra.involute_of_mem_integerGrading z.property,
        Units.smul_def, Units.smul_def, map_zsmul, smul_mul_assoc]
    | add z z' ihz ihz' =>
      rw [map_add, add_mul, map_add, ihz, ihz', map_add, add_mul, map_add, map_add, add_mul]
      abel
  induction x using CliffordAlgebra.induction with
  | algebraMap s => rw [AlgHom.commutes, extDeriv_algebraMap, hFD]
  | ι ω =>
    induction (KaehlerDifferential.span_range_derivation R S ▸ Submodule.mem_top :
        ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S))) using
        Submodule.span_induction with
    | mem _ hω =>
      obtain ⟨s, rfl⟩ := hω
      rw [hFD, hB.sq_zero, extDeriv_ι_D, map_zero]
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, map_add, ih₁, ih₂]
    | smul s ω _ ih =>
      rw [LinearMap.map_smul, Algebra.smul_def, map_mul, AlgHom.commutes,
        hB.toIsNonUnitalDGAlgebra.leibniz_of_mem_zero (hf₀ s), ih, extDeriv_mul,
        extDeriv_algebraMap, AlgHom.commutes, map_add, map_mul, map_mul, hFD, AlgHom.commutes]
  | mul x y ihx ihy =>
    rw [map_mul, hleib, ihx, ihy, extDeriv_mul, map_add, map_mul, map_mul]
  | add x y ihx ihy =>
    rw [map_add, map_add, ihx, ihy, ← map_add F, ← map_add (extDeriv R S)]

end LiftTower

/-- **Universal property of the algebraic de Rham DG algebra**: an `R`-algebra homomorphism
`f : S →ₐ[R] B` into a differential graded `R`-algebra `(B, ℬ, dB)` whose image lies in degree-zero
central elements of `B` and whose degree-one elements square to zero extends to a morphism of
differential graded `R`-algebras `ExteriorAlgebra S Ω[S⁄R] → B`. -/
noncomputable def liftDGAlgHom (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ (s : S) (b : B), f s * b = b * f s)
    (hsq : ∀ b ∈ ℬ 1, b * b = 0) :
    TauCeti.DGAlgHom (isDGAlgebra R S) hB :=
  letI : Algebra S B := f.toRingHom.toAlgebra' hcomm
  letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  { toGradedAlgHom :=
      { toAlgHom := (liftAlgHomAux hB hf₀ hsq).restrictScalars R
        map_mem := liftAlgHomAux_mem hB hf₀ hsq }
    map_d' := liftAlgHomAux_map_d hB hf₀ hsq }

/-- `liftDGAlgHom` extends `f` on degree-zero elements `algebraMap S _ s`. -/
@[simp]
theorem liftDGAlgHom_algebraMap (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ (s : S) (b : B), f s * b = b * f s)
    (hsq : ∀ b ∈ ℬ 1, b * b = 0) (s : S) :
    liftDGAlgHom hB f hf₀ hcomm hsq (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) = f s := by
  let _ : Algebra S B := f.toRingHom.toAlgebra' hcomm
  let _ : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact AlgHom.commutes (liftAlgHomAux hB hf₀ hsq) s

/-- `liftDGAlgHom` sends an exact `1`-form `ι (D R S s)` to `dB (f s)`. -/
@[simp]
theorem liftDGAlgHom_ι_D (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ (s : S) (b : B), f s * b = b * f s)
    (hsq : ∀ b ∈ ℬ 1, b * b = 0) (s : S) :
    liftDGAlgHom hB f hf₀ hcomm hsq (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) =
      dB (f s) := by
  rw [← extDeriv_algebraMap, ← (liftDGAlgHom hB f hf₀ hcomm hsq).map_d, liftDGAlgHom_algebraMap]

end UniversalProperty

section Functoriality

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

private theorem sq_zero_of_mem_grading_one {x : ExteriorAlgebra B Ω[B⁄R]}
    (hx : x ∈ grading R B 1) : x * x = 0 := by
  rw [← Nat.cast_one, mem_grading_natCast, _root_.ExteriorAlgebra.exteriorPower, pow_one] at hx
  obtain ⟨ω, rfl⟩ := hx
  exact ExteriorAlgebra.ι_sq_zero ω

/-- **Functoriality of the algebraic de Rham DG algebra** along an `R`-algebra homomorphism
`f : A →ₐ[R] B`. -/
noncomputable def map (f : A →ₐ[R] B) : TauCeti.DGAlgHom (isDGAlgebra R A) (isDGAlgebra R B) :=
  liftDGAlgHom (isDGAlgebra R B)
    ((IsScalarTower.toAlgHom R B (ExteriorAlgebra B Ω[B⁄R])).comp f)
    (fun a ↦ algebraMap_mem_grading_zero (f a))
    (fun a y ↦ Algebra.commutes (f a) y)
    fun _ hy ↦ sq_zero_of_mem_grading_one hy

/-- On degree-zero elements `algebraMap A _ a`, `map f` applies `f`. -/
@[simp]
theorem map_algebraMap (f : A →ₐ[R] B) (a : A) :
    map f (algebraMap A (ExteriorAlgebra A Ω[A⁄R]) a) =
      algebraMap B (ExteriorAlgebra B Ω[B⁄R]) (f a) :=
  liftDGAlgHom_algebraMap _ _ _ _ _ a

/-- On degree-one generators `ι ω`, `map f` acts through `KaehlerDifferential.mapSemilinear f`. -/
@[simp]
theorem map_ι (f : A →ₐ[R] B) (ω : Ω[A⁄R]) :
    map f (ExteriorAlgebra.ι A ω) =
      ExteriorAlgebra.ι B (KaehlerDifferential.mapSemilinear f ω) := by
  induction (KaehlerDifferential.span_range_derivation R A ▸ Submodule.mem_top :
      ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A))) using
      Submodule.span_induction with
  | mem _ hω =>
    obtain ⟨a, rfl⟩ := hω
    rw [KaehlerDifferential.mapSemilinear_D, ← extDeriv_algebraMap, ← (map f).map_d,
      map_algebraMap, extDeriv_algebraMap]
  | zero => rw [map_zero, map_zero, LinearMap.map_zero, map_zero]
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, ih₁, ih₂]
  | smul a ω _ ih =>
    rw [LinearMap.map_smul, Algebra.smul_def, map_mul, map_algebraMap, ih,
      KaehlerDifferential.mapSemilinear_smul, LinearMap.map_smul, Algebra.smul_def]

/-- `map` carries the identity `R`-algebra homomorphism to the identity `DGAlgHom`. -/
@[simp]
theorem map_id : map (AlgHom.id R A) = TauCeti.DGAlgHom.id (isDGAlgebra R A) :=
  dgAlgHom_ext fun a ↦ by simp

/-- `map` respects composition of `R`-algebra homomorphisms. -/
@[simp]
theorem map_comp (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    map (g.comp f) = (map g).comp (map f) :=
  dgAlgHom_ext fun a ↦ by simp

end Functoriality

/-! ### Coordinate formulas over multivariate polynomial algebras -/

section MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Over a multivariate polynomial ring `MvPolynomial σ R` (with `σ` possibly infinite), the
algebraic exterior derivative of a polynomial `p` is the finite sum over `p.vars` of its formal
partial derivatives wedged with the coordinate differentials `D (X i)`. -/
theorem extDeriv_algebraMap_mvPolynomial_eq_sum_vars (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i ∈ p.vars,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  classical
  rw [extDeriv_algebraMap]
  conv_lhs =>
    rw [← (KaehlerDifferential.mvPolynomialBasis R σ).linearCombination_repr
      (KaehlerDifferential.D R (MvPolynomial σ R) p)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  have hsub : ((KaehlerDifferential.mvPolynomialBasis R σ).repr
      (KaehlerDifferential.D R (MvPolynomial σ R) p)).support ⊆ p.vars := by
    intro i hi
    rw [Finsupp.mem_support_iff, KaehlerDifferential.mvPolynomialBasis_repr_apply] at hi
    by_contra hni
    exact hi (MvPolynomial.pderiv_eq_zero_of_notMem_vars hni)
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.map_smul, KaehlerDifferential.mvPolynomialBasis_repr_apply,
      KaehlerDifferential.mvPolynomialBasis_apply]
  · intro i _ hni
    rw [Finsupp.notMem_support_iff.mp hni, zero_smul, map_zero]

/-- Over a multivariate polynomial ring on a finite variable set `σ`, the exterior derivative of `p`
is `∑ i : σ, pderiv i p • ι (D (X i))`. -/
theorem extDeriv_algebraMap_mvPolynomial [Fintype σ] (p : MvPolynomial σ R) :
    extDeriv R (MvPolynomial σ R)
        (algebraMap (MvPolynomial σ R) (ExteriorAlgebra (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R])
          p) =
      ∑ i : σ,
        MvPolynomial.pderiv i p •
          ExteriorAlgebra.ι (MvPolynomial σ R)
            (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i)) := by
  classical
  rw [extDeriv_algebraMap_mvPolynomial_eq_sum_vars]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ ?_
  rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hi, zero_smul]

/-- Coordinate formula for `extDeriv` on a monomial `1`-form `p • ι (D (X i))` over
`MvPolynomial σ R`, valid without finiteness hypotheses on `σ`. -/
theorem extDeriv_smul_ι_D_X_eq_sum_vars (p : MvPolynomial σ R) (i : σ) :
    extDeriv R (MvPolynomial σ R)
        (p • ExteriorAlgebra.ι (MvPolynomial σ R)
          (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i))) =
      ∑ j ∈ p.vars,
        MvPolynomial.pderiv j p •
          (ExteriorAlgebra.ι (MvPolynomial σ R)
              (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X j)) *
            ExteriorAlgebra.ι (MvPolynomial σ R)
              (KaehlerDifferential.D R (MvPolynomial σ R) (MvPolynomial.X i))) := by
  rw [extDeriv_smul, extDeriv_ι_D, smul_zero, add_zero, ← extDeriv_algebraMap,
    extDeriv_algebraMap_mvPolynomial_eq_sum_vars, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_mul_assoc]

end MvPolynomial

end TauCeti.KaehlerDeRham
