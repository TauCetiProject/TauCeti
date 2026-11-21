/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.LinearAlgebra.ExteriorAlgebra.IntegerGrading
public import TauCeti.RingTheory.Kaehler.Basic
public import TauCeti.RingTheory.Kaehler.MapSemilinear
import TauCeti.Algebra.Algebra.Subalgebra.Centralizer
import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation
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
for `R`-algebra maps `f : S →ₐ[R] B` into a differential graded `R`-algebra `(B, ℬ, dB)` whose
values lie in degree zero, commute with the differentials `dB (f t)`, and have square-zero
differentials `dB (f s) * dB (f s) = 0`; and establish covariant functoriality (`map`) along
arbitrary `R`-algebra homomorphisms, acting on `1`-forms through
`KaehlerDifferential.mapSemilinear` (`map_ι`).

## Main definitions

* `TauCeti.KaehlerDeRham.grading R S`: the `ℤ`-grading of `ExteriorAlgebra S Ω[S⁄R]` as an
  `R`-algebra, obtained by restricting scalars from `TauCeti.ExteriorAlgebra.integerGrading`.
* `TauCeti.KaehlerDeRham.extDeriv R S`: the algebraic exterior derivative on
  `ExteriorAlgebra S Ω[S⁄R]`, as an `R`-linear endomorphism.
* `TauCeti.KaehlerDeRham.liftDGAlgHom`: universal property lifting an `R`-algebra homomorphism
  `f : S →ₐ[R] B` into degree zero of a DG `R`-algebra `(B, ℬ, dB)` with
  `f s * dB (f t) = dB (f t) * f s` and `dB (f s) * dB (f s) = 0` to a morphism of DG `R`-algebras
  out of `ExteriorAlgebra S Ω[S⁄R]`.
* `TauCeti.KaehlerDeRham.map`: functoriality of the algebraic de Rham DG algebra along an
  `R`-algebra homomorphism `A →ₐ[R] B`.

## Main results

* `TauCeti.KaehlerDeRham.inductionOn`: algebra induction on `ExteriorAlgebra S Ω[S⁄R]` from degree
  zero (`algebraMap S _ s`) and exact `1`-forms (`ι (D R S s)`).
* `TauCeti.KaehlerDeRham.extDeriv_mul`, `extDeriv_mul_of_mem_exteriorPower`,
  `extDeriv_mul_of_mem_grading`: the graded Leibniz rule for `extDeriv R S`.
* `TauCeti.KaehlerDeRham.extDeriv_extDeriv`, `extDeriv_comp_extDeriv`: `extDeriv R S` squares to
  zero.
* `TauCeti.KaehlerDeRham.isDGAlgebra`: `ExteriorAlgebra S Ω[S⁄R]` is a differential graded
  `R`-algebra under `grading R S` and `extDeriv R S`.
* `TauCeti.KaehlerDeRham.extDeriv_unique`, `extDeriv_unique_of_isDGAlgebra`: uniqueness of the
  algebraic exterior derivative.
* `TauCeti.KaehlerDeRham.dgAlgHom_ext`, `dgAlgHom_ext_iff`, `eq_liftDGAlgHom_iff`: two DG algebra
  morphisms out of `ExteriorAlgebra S Ω[S⁄R]` agree if and only if they agree on `S`, and
  uniqueness in the universal property of `liftDGAlgHom`.

## Implementation notes

To avoid division by `2` or basis hypotheses, `extDeriv R S` is constructed in two steps:

1. Using `TauCeti.KaehlerDifferential.liftOfKerTotal`, the `R`-linear map on `S →₀ S` sending
   `single x c` to `ι (D c) * ι (D x)` descends to `extDerivOne : Ω[S⁄R] →ₗ[R] ExteriorAlgebra S
   Ω[S⁄R]`, taking values in `⋀[S]^2 Ω[S⁄R]`, vanishing on `D x`, and satisfying
   `extDerivOne (s • ω) = ι (D s) * ι ω + s • extDerivOne ω`.
2. Applying `ExteriorAlgebra.liftTwistedDerivation` with twist `σ = involute`, degree-zero
   derivation `ι ∘ D R S`, and degree-one map `extDerivOne` extends this data to the odd graded
   `R`-linear derivation `extDeriv R S` without division by `2` or `SMul S` diamonds.

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

/-- Unfolding lemma expressing `grading R S p` as the `R`-scalar restriction of
`TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R] p`. -/
theorem grading_def (p : ℤ) :
    grading R S p = (TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R] p).restrictScalars R := by
  rfl

/-- In nonnegative degree `n`, `grading R S n` is the `R`-scalar restriction of the `n`-th exterior
power `⋀[S]^n Ω[S⁄R]`. -/
@[simp]
theorem grading_natCast (n : ℕ) :
    grading R S (n : ℕ) = (⋀[S]^n Ω[S⁄R]).restrictScalars R := by
  rw [grading_def, TauCeti.ExteriorAlgebra.integerGrading_natCast]

/-- Membership in `grading R S p` agrees with membership in the `S`-linear integer grading. -/
@[simp]
theorem mem_grading_iff {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} :
    x ∈ grading R S p ↔ x ∈ TauCeti.ExteriorAlgebra.integerGrading S Ω[S⁄R] p := by
  simp [grading]

/-- In nonnegative degree `n`, `grading R S n` is the `n`-th exterior power `⋀[S]^n Ω[S⁄R]`. -/
theorem mem_grading_natCast {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]} :
    x ∈ grading R S n ↔ x ∈ ⋀[S]^n Ω[S⁄R] := by
  simp

/-- The grading of `ExteriorAlgebra S Ω[S⁄R]` vanishes in negative degrees. -/
theorem grading_of_neg {p : ℤ} (hp : p < 0) : grading R S p = ⊥ := by
  ext x
  simp [TauCeti.ExteriorAlgebra.integerGrading_of_neg hp]

/-- The grade involution acts on the degree-`p` piece `grading R S p` by `p.negOnePow`. -/
theorem involute_of_mem_grading {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]}
    (hx : x ∈ grading R S p) :
    involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x = p.negOnePow • x :=
  TauCeti.ExteriorAlgebra.involute_of_mem_integerGrading (mem_grading_iff.mp hx)

/-- Elements of `S` sit in degree zero of the algebraic de Rham grading. -/
theorem algebraMap_mem_grading_zero (s : S) :
    algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s ∈ grading R S 0 := by
  rw [← Nat.cast_zero, mem_grading_natCast, _root_.ExteriorAlgebra.exteriorPower, pow_zero]
  exact Submodule.algebraMap_mem s

/-- Kähler `1`-forms sit in degree one of the algebraic de Rham grading. -/
theorem ι_mem_grading_one (ω : Ω[S⁄R]) :
    ExteriorAlgebra.ι S ω ∈ grading R S 1 :=
  mem_grading_iff.mpr (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one ω)

/-- **Algebra induction on the algebraic de Rham complex `ExteriorAlgebra S Ω[S⁄R]`**: to prove a
predicate on `x : ExteriorAlgebra S Ω[S⁄R]`, it suffices to check it on degree-zero scalars
`algebraMap S _ s` and exact `1`-forms `ι (D R S s)`, and show closure under multiplication and
addition. -/
@[elab_as_elim]
theorem inductionOn {motive : ExteriorAlgebra S Ω[S⁄R] → Prop} (x : ExteriorAlgebra S Ω[S⁄R])
    (algebraMap : ∀ s : S, motive (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s))
    (ι_D : ∀ s : S, motive (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)))
    (mul : ∀ x y : ExteriorAlgebra S Ω[S⁄R], motive x → motive y → motive (x * y))
    (add : ∀ x y : ExteriorAlgebra S Ω[S⁄R], motive x → motive y → motive (x + y)) :
    motive x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap s => exact algebraMap s
  | ι ω =>
    induction ω using KaehlerDifferential.inductionOn with
    | D s => exact ι_D s
    | smul s ω ih =>
      rw [LinearMap.map_smul, Algebra.smul_def]
      exact mul _ _ (algebraMap s) ih
    | add _ _ ih₁ ih₂ =>
      rw [map_add]
      exact add _ _ ih₁ ih₂
  | mul x y ihx ihy => exact mul x y ihx ihy
  | add x y ihx ihy => exact add x y ihx ihy

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
    simp only [smul_add, map_add, mul_add, ih₁, ih₂]
    abel
  | single x c =>
    simp [Finsupp.smul_single, preExtDerivOne_single, Derivation.leibniz, add_mul]

private theorem preExtDerivOne_eq_zero_of_mem_kerTotal {v : S →₀ S}
    (hv : v ∈ KaehlerDifferential.kerTotal R S) : preExtDerivOne R S v = 0 :=
  TauCeti.KaehlerDifferential.map_eq_zero_of_mem_kerTotal (preExtDerivOne R S)
    (fun _ _ ↦ by simp [preExtDerivOne_single])
    (fun _ _ ↦ by
      simp only [map_sub, map_add, preExtDerivOne_single, Derivation.map_one_eq_zero, map_zero,
        zero_mul, sub_zero]
      exact ExteriorAlgebra.ι_add_mul_swap _ _)
    (fun _ ↦ by simp [preExtDerivOne_single])
    (fun s v hker ih ↦ by simp [preExtDerivOne_smul, ih, hker])
    hv

/-- Auxiliary degree-one exterior derivative `Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R]`. -/
private noncomputable def extDerivOne : Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R] :=
  TauCeti.KaehlerDifferential.liftOfKerTotal R (preExtDerivOne R S)
    fun _ hv ↦ preExtDerivOne_eq_zero_of_mem_kerTotal R S hv

private theorem extDerivOne_D (x : S) :
    extDerivOne R S (KaehlerDifferential.D R S x) = 0 := by
  simp [extDerivOne, preExtDerivOne_single]

private theorem extDerivOne_smul (s : S) (ω : Ω[S⁄R]) :
    extDerivOne R S (s • ω) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) * ExteriorAlgebra.ι S ω +
        s • extDerivOne R S ω := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R S ω
  rw [← LinearMap.map_smul, extDerivOne,
    TauCeti.KaehlerDifferential.liftOfKerTotal_linearCombination,
    TauCeti.KaehlerDifferential.liftOfKerTotal_linearCombination, preExtDerivOne_smul, add_comm]

private theorem extDerivOne_mem_exteriorPower_two (ω : Ω[S⁄R]) :
    extDerivOne R S ω ∈ ⋀[S]^2 Ω[S⁄R] := by
  induction ω using KaehlerDifferential.inductionOn with
  | D x =>
    rw [extDerivOne_D]
    exact zero_mem _
  | smul s ω ih =>
    rw [extDerivOne_smul]
    exact add_mem
      (SetLike.mul_mem_graded (ExteriorAlgebra.ι_mem_exteriorPower_one _)
        (ExteriorAlgebra.ι_mem_exteriorPower_one _))
      (Submodule.smul_mem _ s ih)
  | add _ _ ih₁ ih₂ =>
    rw [map_add]
    exact add_mem ih₁ ih₂

private theorem extDerivOne_mul_ι_add_involute_ι_mul (ω : Ω[S⁄R]) :
    extDerivOne R S ω * ExteriorAlgebra.ι S ω +
      involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (ExteriorAlgebra.ι S ω) *
        extDerivOne R S ω = 0 := by
  have hinv : involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (extDerivOne R S ω) =
      extDerivOne R S ω := by
    rw [TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower
      (extDerivOne_mem_exteriorPower_two R S ω)]
    simp
  rw [involute_ι, neg_mul, ExteriorAlgebra.ι_mul_eq_involute_mul, hinv, add_neg_cancel]

/-- **The algebraic exterior derivative** on the algebraic de Rham algebra
`ExteriorAlgebra S Ω[S⁄R]`, the unique `R`-linear endomorphism extending
`KaehlerDifferential.D R S` in degree zero, annihilating exact `1`-forms `ι (D R S s)`, and
satisfying `extDeriv R S (x * y) = extDeriv R S x * y + involute x * extDeriv R S y`. -/
noncomputable def extDeriv : ExteriorAlgebra S Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R] :=
  ExteriorAlgebra.liftTwistedDerivation
    (involute (Q := (0 : QuadraticForm S Ω[S⁄R])))
    ((ExteriorAlgebra.ι S).compDer (KaehlerDifferential.D R S))
    (fun s ω ↦ by
      simpa using ExteriorAlgebra.ι_mul_eq_involute_mul (KaehlerDifferential.D R S s)
        (ExteriorAlgebra.ι S ω))
    (extDerivOne R S)
    (fun s ω ↦ by simpa using extDerivOne_smul R S s ω)
    (extDerivOne_mul_ι_add_involute_ι_mul R S)

variable {R S}

private theorem extDeriv_ι_eq_extDerivOne (ω : Ω[S⁄R]) :
    extDeriv R S (ExteriorAlgebra.ι S ω) = extDerivOne R S ω := by
  simp [extDeriv]

/-- On degree-zero elements `algebraMap S _ s`, the exterior derivative is the universal Kähler
differential `ι (D R S s)`. -/
@[simp]
theorem extDeriv_algebraMap (s : S) :
    extDeriv R S (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) := by
  simp [extDeriv]

/-- The exterior derivative annihilates `1`. -/
@[simp]
theorem extDeriv_one : extDeriv R S 1 = 0 := by
  simp [extDeriv]

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
        involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x * extDeriv R S y :=
  ExteriorAlgebra.liftTwistedDerivation_mul _ _ _ _ _ _ x y

/-- Scalar multiplication by `s : S` satisfies the Leibniz rule
`extDeriv R S (s • x) = ι (D R S s) * x + s • extDeriv R S x`. -/
@[simp]
theorem extDeriv_smul (s : S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (s • x) =
      ExteriorAlgebra.ι S (KaehlerDifferential.D R S s) * x + s • extDeriv R S x := by
  simp [extDeriv]

/-- The graded Leibniz rule for a left factor in the `n`-th exterior power `⋀[S]^n Ω[S⁄R]`. -/
theorem extDeriv_mul_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]}
    (hx : x ∈ ⋀[S]^n Ω[S⁄R]) (y : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (x * y) = extDeriv R S x * y + (-1 : S) ^ n • (x * extDeriv R S y) := by
  rw [extDeriv_mul, TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower hx, smul_mul_assoc]

/-- The graded Leibniz rule for a homogeneous left factor of integer degree `p`. -/
theorem extDeriv_mul_of_mem_grading {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]}
    (hx : x ∈ grading R S p) (y : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (x * y) = extDeriv R S x * y + p.negOnePow • (x * extDeriv R S y) := by
  rw [extDeriv_mul, involute_of_mem_grading hx, smul_mul_assoc]

/-- `extDeriv R S` carries `⋀[S]^n Ω[S⁄R]` into `⋀[S]^(n + 1) Ω[S⁄R]`. -/
theorem extDeriv_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra S Ω[S⁄R]}
    (hx : x ∈ ⋀[S]^n Ω[S⁄R]) : extDeriv R S x ∈ ⋀[S]^(n + 1) Ω[S⁄R] :=
  ExteriorAlgebra.liftTwistedDerivation_mem_exteriorPower _ _ _ _ _ _ (r := 1)
    (fun ω ↦ by rw [involute_ι]; exact neg_mem (ExteriorAlgebra.ι_mem_exteriorPower_one ω))
    (fun s ↦ ExteriorAlgebra.ι_mem_exteriorPower_one _)
    (extDerivOne_mem_exteriorPower_two R S) hx

/-- `extDeriv R S` raises the integer degree in `grading R S` by one. -/
theorem extDeriv_mem_grading {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S p) :
    extDeriv R S x ∈ grading R S (p + 1) :=
  mem_grading_iff.mpr <|
    ExteriorAlgebra.liftTwistedDerivation_mem_integerGrading _ _ _ _ _ _ (r := 1)
      (fun ω ↦ by
        rw [involute_ι]
        exact neg_mem (TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one ω))
      (fun s ↦ TauCeti.ExteriorAlgebra.ι_mem_integerGrading_one _)
      (fun ω ↦ by
        rw [one_add_one_eq_two, ← Nat.cast_ofNat (n := 2),
          TauCeti.ExteriorAlgebra.integerGrading_natCast]
        exact extDerivOne_mem_exteriorPower_two R S ω)
      (mem_grading_iff.mp hx)

/-- `extDeriv R S` anticommutes with the grade involution on `ExteriorAlgebra S Ω[S⁄R]`. -/
theorem extDeriv_involute (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) x) =
      -involute (Q := (0 : QuadraticForm S Ω[S⁄R])) (extDeriv R S x) := by
  simpa using ExteriorAlgebra.map_involute_of_map_mem_integerGrading (extDeriv R S) 1
    (fun hx ↦ mem_grading_iff.mp (extDeriv_mem_grading (mem_grading_iff.mpr hx))) x

/-- **The exterior derivative squares to zero** in arbitrary characteristic. -/
@[simp]
theorem extDeriv_extDeriv (x : ExteriorAlgebra S Ω[S⁄R]) :
    extDeriv R S (extDeriv R S x) = 0 := by
  induction x using inductionOn with
  | algebraMap s => rw [extDeriv_algebraMap, extDeriv_ι_D]
  | ι_D s => rw [extDeriv_ι_D, map_zero]
  | mul x y ihx ihy =>
    simp only [extDeriv_mul, map_add, extDeriv_involute, involute_involute, ihx, ihy, zero_mul,
      mul_zero, neg_mul]
    abel
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy, add_zero]

/-- As an `R`-linear endomorphism, `extDeriv R S` composes with itself to zero. -/
@[simp]
theorem extDeriv_comp_extDeriv : (extDeriv R S).comp (extDeriv R S) = 0 :=
  LinearMap.ext extDeriv_extDeriv

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
  induction x using inductionOn with
  | algebraMap s => rw [h_alg, extDeriv_algebraMap]
  | ι_D s => rw [← h_alg s, h_sq s, h_alg s, extDeriv_ι_D]
  | mul x y ihx ihy => rw [h_mul, extDeriv_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

/-- For any grading-preserving `R`-algebra homomorphism `F` from `ExteriorAlgebra S Ω[S⁄R]` into a
differential graded `R`-algebra `(B, ℬ, dB)`, `dB` obeys the `involute`-twisted Leibniz rule on
products `F z * b`. -/
private theorem d_mul_eq_involute {B : Type*} [Ring B] [Algebra R B]
    {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}
    (hB : TauCeti.IsDGAlgebra ℬ dB) (F : ExteriorAlgebra S Ω[S⁄R] →ₐ[R] B)
    (hF : ∀ {p : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]}, x ∈ grading R S p → F x ∈ ℬ p)
    (z : ExteriorAlgebra S Ω[S⁄R]) (b : B) :
    dB (F z * b) =
      dB (F z) * b + F (involute (Q := (0 : QuadraticForm S Ω[S⁄R])) z) * dB b := by
  induction z using DirectSum.Decomposition.inductionOn (grading R S) with
  | zero => simp
  | homogeneous z =>
    rw [hB.leibniz (hF z.property), involute_of_mem_grading z.property, Units.smul_def,
      Units.smul_def, map_zsmul, smul_mul_assoc]
  | add z z' ihz ihz' =>
    simp only [map_add, add_mul, ihz, ihz']
    abel

/-- A differential making `(ExteriorAlgebra S Ω[S⁄R], grading R S)` a differential graded
`R`-algebra and extending `ι ∘ D R S` on `S` is necessarily `extDeriv R S`. -/
theorem extDeriv_unique_of_isDGAlgebra
    {d : ExteriorAlgebra S Ω[S⁄R] →ₗ[R] ExteriorAlgebra S Ω[S⁄R]}
    (hd : TauCeti.IsDGAlgebra (grading R S) d)
    (h_alg : ∀ s : S,
      d (algebraMap S _ s) = ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) :
    d = extDeriv R S :=
  extDeriv_unique h_alg (fun _ ↦ hd.sq_zero _) fun x y ↦
    d_mul_eq_involute hd (AlgHom.id R _) (fun hx ↦ hx) x y

end Construction

/-! ### Universal property and functoriality -/

section UniversalProperty

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [Ring B] [Algebra R B]
  {ℬ : ℤ → Submodule R B} [GradedAlgebra ℬ] {dB : B →ₗ[R] B}

/-- **Extensionality of DG algebra morphisms out of the algebraic de Rham complex**: two DG algebra
morphisms out of `ExteriorAlgebra S Ω[S⁄R]` agree as soon as they agree on degree zero (`S`). -/
@[ext]
theorem dgAlgHom_ext {hB : TauCeti.IsDGAlgebra ℬ dB}
    {Φ Ψ : TauCeti.DGAlgHom (isDGAlgebra R S) hB}
    (h : ∀ s : S,
      Φ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) =
        Ψ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s)) :
    Φ = Ψ := by
  ext x
  induction x using inductionOn with
  | algebraMap s => exact h s
  | ι_D s => rw [← extDeriv_algebraMap, ← Φ.map_d, ← Ψ.map_d, h s]
  | mul x y ihx ihy => rw [map_mul, map_mul, ihx, ihy]
  | add x y ihx ihy => rw [map_add, map_add, ihx, ihy]

section LiftCentralizer

private theorem dB_mul_add_mul_dB (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (s t : S) :
    dB (f s) * dB (f t) + dB (f t) * dB (f s) = 0 := by
  have h := congrArg dB (hcomm s t)
  simp only [hB.toIsNonUnitalDGAlgebra.leibniz_of_mem_zero (hf₀ s),
    hB.leibniz (hB.map_mem (hf₀ t)), hB.sq_zero, mul_zero, add_zero, zero_mul, zero_add,
    Int.negOnePow_one, Units.smul_def, Units.val_neg, Units.val_one, neg_one_zsmul] at h
  exact eq_neg_iff_add_eq_zero.mp h

private theorem dB_mem_centralizer (f : S →ₐ[R] B)
    (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s) (t : S) :
    dB (f t) ∈ Subalgebra.centralizer R (Set.range f) := by
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨s, rfl⟩
  exact hcomm s t

private noncomputable def liftAlgHomAuxWithSpec (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) :
    { F : ExteriorAlgebra S Ω[S⁄R] →ₐ[R] B //
      (∀ s : S, F (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) = f s) ∧
      (∀ s : S, F (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) = dB (f s)) } :=
  let C := Subalgebra.centralizer R (Set.range f)
  let fC : S →ₐ[R] C := f.codRestrict C (Subalgebra.apply_mem_centralizer_range R f)
  letI : Algebra S C :=
    fC.toRingHom.toAlgebra' fun s c ↦ Subtype.ext <|
      (Subalgebra.mem_centralizer_iff R).mp c.property (f s) ⟨s, rfl⟩
  letI : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' fC.comp_algebraMap.symm
  let D₀ : Derivation R S C :=
    { toFun := fun s ↦ ⟨dB (f s), dB_mem_centralizer f hcomm s⟩
      map_add' := fun s t ↦ Subtype.ext <| by simp
      map_smul' := fun r s ↦ Subtype.ext <| by simp
      map_one_eq_zero' := Subtype.ext <| by simp [hB.map_one_eq_zero]
      leibniz' := fun s t ↦ Subtype.ext <| by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra', fC,
          hB.toIsNonUnitalDGAlgebra.leibniz_of_mem_zero (hf₀ s), hcomm t s, add_comm] }
  let φ : Ω[S⁄R] →ₗ[S] C := D₀.liftKaehlerDifferential
  have hanti : ∀ ω₁ ω₂ : Ω[S⁄R], φ ω₁ * φ ω₂ + φ ω₂ * φ ω₁ = 0 := by
    intro ω₁ ω₂
    induction ω₁ using KaehlerDifferential.inductionOn with
    | D s =>
      induction ω₂ using KaehlerDifferential.inductionOn with
      | D t =>
        exact Subtype.ext <| by
          simpa [φ, D₀] using dB_mul_add_mul_dB hB f hf₀ hcomm s t
      | smul t ω₂ ih =>
        rw [LinearMap.map_smul, mul_smul_comm, smul_mul_assoc, ← smul_add, ih, smul_zero]
      | add _ _ ih₁ ih₂ =>
        simp only [map_add, mul_add, add_mul]
        rw [add_add_add_comm, ih₁, ih₂, add_zero]
    | smul s ω₁ ih =>
      rw [LinearMap.map_smul, smul_mul_assoc, mul_smul_comm, ← smul_add, ih, smul_zero]
    | add _ _ ih₁ ih₂ =>
      simp only [map_add, add_mul, mul_add]
      rw [add_add_add_comm, ih₁, ih₂, add_zero]
  have hφ_sq : ∀ ω : Ω[S⁄R], φ ω * φ ω = 0 := by
    intro ω
    induction ω using KaehlerDifferential.inductionOn with
    | D s => exact Subtype.ext <| by simpa [φ, D₀] using hsq s
    | smul s ω ih =>
      simp only [LinearMap.map_smul, smul_mul_assoc, mul_smul_comm, ih, smul_zero]
    | add ω₁ ω₂ ih₁ ih₂ =>
      simp only [map_add, add_mul, mul_add, ih₁, ih₂, zero_add, add_zero]
      exact hanti ω₂ ω₁
  ⟨C.val.comp ((ExteriorAlgebra.lift S ⟨φ, hφ_sq⟩).restrictScalars R),
    fun s ↦ congrArg Subtype.val (AlgHom.commutes (ExteriorAlgebra.lift S ⟨φ, hφ_sq⟩) s),
    fun s ↦ by
      rw [AlgHom.comp_apply, AlgHom.coe_restrictScalars', ExteriorAlgebra.lift_ι_apply]
      exact congrArg Subtype.val (D₀.liftKaehlerDifferential_comp_D s)⟩

private noncomputable def liftAlgHomAux (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) :
    ExteriorAlgebra S Ω[S⁄R] →ₐ[R] B :=
  (liftAlgHomAuxWithSpec hB f hf₀ hcomm hsq).val

private theorem liftAlgHomAux_algebraMap (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) (s : S) :
    liftAlgHomAux hB f hf₀ hcomm hsq (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) = f s :=
  (liftAlgHomAuxWithSpec hB f hf₀ hcomm hsq).property.1 s

private theorem liftAlgHomAux_ι_D (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) (s : S) :
    liftAlgHomAux hB f hf₀ hcomm hsq (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) =
      dB (f s) :=
  (liftAlgHomAuxWithSpec hB f hf₀ hcomm hsq).property.2 s

private theorem liftAlgHomAux_ι_mem_one (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) (ω : Ω[S⁄R]) :
    liftAlgHomAux hB f hf₀ hcomm hsq (ExteriorAlgebra.ι S ω) ∈ ℬ 1 := by
  induction ω using KaehlerDifferential.inductionOn with
  | D s =>
    rw [liftAlgHomAux_ι_D]
    simpa using hB.map_mem (hf₀ s)
  | smul s ω ih =>
    rw [LinearMap.map_smul, Algebra.smul_def, map_mul, liftAlgHomAux_algebraMap]
    simpa using SetLike.mul_mem_graded (hf₀ s) ih
  | add _ _ ih₁ ih₂ =>
    rw [map_add, map_add]
    exact add_mem ih₁ ih₂

private theorem liftAlgHomAux_mem (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0)
    {i : ℤ} {x : ExteriorAlgebra S Ω[S⁄R]} (hx : x ∈ grading R S i) :
    liftAlgHomAux hB f hf₀ hcomm hsq x ∈ ℬ i := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [grading_of_neg hi, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    clear hi
    rw [mem_grading_natCast] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap s =>
      rw [Nat.cast_zero, liftAlgHomAux_algebraMap]
      exact hf₀ s
    | add x y k _ _ ihx ihy =>
      rw [map_add]
      exact add_mem ihx ihy
    | mem_mul m hm k x _ ih =>
      obtain ⟨ω, rfl⟩ := hm
      have hk : ((k + 1 : ℕ) : ℤ) = 1 + (k : ℤ) := by rw [Nat.cast_add_one, add_comm]
      rw [map_mul, hk]
      exact SetLike.mul_mem_graded (liftAlgHomAux_ι_mem_one hB f hf₀ hcomm hsq ω) ih

private theorem liftAlgHomAux_map_d (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) (x : ExteriorAlgebra S Ω[S⁄R]) :
    dB (liftAlgHomAux hB f hf₀ hcomm hsq x) =
      liftAlgHomAux hB f hf₀ hcomm hsq (extDeriv R S x) := by
  induction x using inductionOn with
  | algebraMap s => rw [liftAlgHomAux_algebraMap, extDeriv_algebraMap, liftAlgHomAux_ι_D]
  | ι_D s => rw [liftAlgHomAux_ι_D, hB.sq_zero, extDeriv_ι_D, map_zero]
  | mul x y ihx ihy =>
    simp only [map_mul,
      d_mul_eq_involute hB (liftAlgHomAux hB f hf₀ hcomm hsq)
        (liftAlgHomAux_mem hB f hf₀ hcomm hsq),
      ihx, ihy, extDeriv_mul, map_add]
  | add x y ihx ihy => simp only [map_add, ihx, ihy]

end LiftCentralizer

/-- **Universal property of the algebraic de Rham DG algebra**: an `R`-algebra homomorphism
`f : S →ₐ[R] B` into a differential graded `R`-algebra `(B, ℬ, dB)` whose image lies in degree
zero, commutes with the differentials `dB (f t)`, and satisfies `dB (f s) * dB (f s) = 0` extends
to a morphism of differential graded `R`-algebras `ExteriorAlgebra S Ω[S⁄R] → B`. -/
noncomputable def liftDGAlgHom (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) :
    TauCeti.DGAlgHom (isDGAlgebra R S) hB where
  toGradedAlgHom :=
    { toAlgHom := liftAlgHomAux hB f hf₀ hcomm hsq
      map_mem := liftAlgHomAux_mem hB f hf₀ hcomm hsq }
  map_d' := liftAlgHomAux_map_d hB f hf₀ hcomm hsq

/-- `liftDGAlgHom` extends `f` on degree-zero elements `algebraMap S _ s`. -/
@[simp]
theorem liftDGAlgHom_algebraMap (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) (s : S) :
    liftDGAlgHom hB f hf₀ hcomm hsq (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) = f s :=
  liftAlgHomAux_algebraMap hB f hf₀ hcomm hsq s

/-- `liftDGAlgHom` sends an exact `1`-form `ι (D R S s)` to `dB (f s)`. -/
@[simp]
theorem liftDGAlgHom_ι_D (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) (s : S) :
    liftDGAlgHom hB f hf₀ hcomm hsq (ExteriorAlgebra.ι S (KaehlerDifferential.D R S s)) =
      dB (f s) :=
  liftAlgHomAux_ι_D hB f hf₀ hcomm hsq s

/-- `liftDGAlgHom` turns `S`-scalar multiplication into left multiplication by `f s`. -/
@[simp]
theorem liftDGAlgHom_smul (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0) (s : S) (x : ExteriorAlgebra S Ω[S⁄R]) :
    liftDGAlgHom hB f hf₀ hcomm hsq (s • x) =
      f s * liftDGAlgHom hB f hf₀ hcomm hsq x := by
  rw [Algebra.smul_def, map_mul, liftDGAlgHom_algebraMap]

/-- **Uniqueness in the universal property of the algebraic de Rham DG algebra**: a DG algebra
morphism out of `ExteriorAlgebra S Ω[S⁄R]` equals `liftDGAlgHom hB f hf₀ hcomm hsq` if and only if
it extends `f` on degree-zero elements `algebraMap S _ s`. -/
theorem eq_liftDGAlgHom_iff (hB : TauCeti.IsDGAlgebra ℬ dB) (f : S →ₐ[R] B)
    (hf₀ : ∀ s : S, f s ∈ ℬ 0) (hcomm : ∀ s t : S, f s * dB (f t) = dB (f t) * f s)
    (hsq : ∀ s : S, dB (f s) * dB (f s) = 0)
    {Φ : TauCeti.DGAlgHom (isDGAlgebra R S) hB} :
    Φ = liftDGAlgHom hB f hf₀ hcomm hsq ↔
      ∀ s : S, Φ (algebraMap S (ExteriorAlgebra S Ω[S⁄R]) s) = f s := by
  simp [TauCeti.KaehlerDeRham.dgAlgHom_ext_iff]

end UniversalProperty

section Functoriality

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- **Functoriality of the algebraic de Rham DG algebra** along an `R`-algebra homomorphism
`f : A →ₐ[R] B`. -/
noncomputable def map (f : A →ₐ[R] B) : TauCeti.DGAlgHom (isDGAlgebra R A) (isDGAlgebra R B) :=
  liftDGAlgHom (isDGAlgebra R B)
    ((IsScalarTower.toAlgHom R B (ExteriorAlgebra B Ω[B⁄R])).comp f)
    (fun a ↦ algebraMap_mem_grading_zero (f a))
    (fun a₁ _ ↦ Algebra.commutes (f a₁) _)
    fun a ↦ by
      simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, extDeriv_algebraMap]
      exact ExteriorAlgebra.ι_sq_zero _

/-- On degree-zero elements `algebraMap A _ a`, `map f` applies `f`. -/
@[simp]
theorem map_algebraMap (f : A →ₐ[R] B) (a : A) :
    map f (algebraMap A (ExteriorAlgebra A Ω[A⁄R]) a) =
      algebraMap B (ExteriorAlgebra B Ω[B⁄R]) (f a) :=
  liftDGAlgHom_algebraMap _ _ _ _ _ a

/-- `map f` is `f`-semilinear with respect to scalar multiplication by `A` and `B`. -/
@[simp]
theorem map_smul (f : A →ₐ[R] B) (a : A) (x : ExteriorAlgebra A Ω[A⁄R]) :
    map f (a • x) = f a • map f x := by
  rw [Algebra.smul_def, map_mul, map_algebraMap, ← Algebra.smul_def]

/-- On degree-one generators `ι ω`, `map f` acts through `KaehlerDifferential.mapSemilinear f`. -/
@[simp]
theorem map_ι (f : A →ₐ[R] B) (ω : Ω[A⁄R]) :
    map f (ExteriorAlgebra.ι A ω) =
      ExteriorAlgebra.ι B (KaehlerDifferential.mapSemilinear f ω) := by
  induction ω using KaehlerDifferential.inductionOn with
  | D a =>
    rw [KaehlerDifferential.mapSemilinear_D, ← extDeriv_algebraMap, ← (map f).map_d,
      map_algebraMap, extDeriv_algebraMap]
  | smul a ω ih =>
    simp only [LinearMap.map_smul, map_smul, ih, KaehlerDifferential.mapSemilinear_smul]
  | add _ _ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

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

end TauCeti.KaehlerDeRham
