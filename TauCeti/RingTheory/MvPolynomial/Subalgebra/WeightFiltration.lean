/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Flat
public import TauCeti.RingTheory.MvPolynomial.WeightFiltration
import TauCeti.Algebra.Polynomial.AlgHom

/-!
# The induced weight filtration on a polynomial subalgebra

For a subalgebra `A` of a multivariate polynomial ring, pull back the ambient weight
filtration to `A`. Its Rees algebra is realized inside `A[t]` using `coeffSubalgebra`.
The coefficientwise embedding into the ambient polynomial ring identifies it with the
intersection of the ambient weight Rees algebra and `A[t]`, induces the canonical inclusion
`Subalgebra.weightReesInclusion` into `TauCeti.MvPolynomial.weightReesAlgebra R w`, and makes
`A ↦ A.weightReesAlgebra w` functorial in `A ≤ B` (`Subalgebra.weightReesMap`). When each
`c i ∈ A` has ambient `w`-weight at most `d i`, the Rees presentation map `weightReesAeval c d`
(`Y i ↦ c i * t ^ d i`, `t ↦ t`) lifts to an `R[t]`-algebra homomorphism
`TauCeti.MvPolynomial.weightReesAevalLift` into `A.weightReesAlgebra w` with the same kernel as
`weightReesAeval c d`.

Over a field this Rees algebra is flat over `k[t]`, without any finite generation or SAGBI
hypothesis. The increasing and exhaustive filtration also permits applying the shared
`coeffSubalgebra` unit-fibre comparisons.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, AMS, 1996, Chapter 11.
* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, §15.8.
-/

public section

open scoped Polynomial
open TauCeti TauCeti.MvPolynomial

namespace Subalgebra

variable {σ R : Type*} [CommSemiring R] (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ)

/-- The ambient weight filtration restricted to a polynomial subalgebra. -/
noncomputable def weightFiltration (n : ℕ) : Submodule R A :=
  (TauCeti.MvPolynomial.weightFiltration R w n).comap A.val.toLinearMap

/-- Membership in the induced filtration is the ambient weight bound. -/
@[simp]
theorem mem_weightFiltration_iff {n : ℕ} {f : A} :
    f ∈ A.weightFiltration w n ↔
      (f : MvPolynomial σ R) ∈ TauCeti.MvPolynomial.weightFiltration R w n :=
  Iff.rfl

/-- The lower stages of the induced weight filtration. -/
noncomputable def weightFiltrationLT (n : ℕ) : Submodule R A :=
  (TauCeti.MvPolynomial.weightFiltrationLT R w n).comap A.val.toLinearMap

/-- Membership in a lower stage is the strict ambient weight bound. -/
@[simp]
theorem mem_weightFiltrationLT_iff {n : ℕ} {f : A} :
    f ∈ A.weightFiltrationLT w n ↔
      (f : MvPolynomial σ R) ∈ TauCeti.MvPolynomial.weightFiltrationLT R w n :=
  Iff.rfl

/-- The induced weight filtration is multiplicative. -/
instance weightFiltrationGradedMonoid : SetLike.GradedMonoid (A.weightFiltration w) where
  one_mem := by
    simpa using (SetLike.GradedOne.one_mem :
      (1 : MvPolynomial σ R) ∈ TauCeti.MvPolynomial.weightFiltration R w 0)
  mul_mem {i j} {f g} hf hg := by
    simpa using SetLike.mul_mem_graded
      ((A.mem_weightFiltration_iff w).mp hf) ((A.mem_weightFiltration_iff w).mp hg)

/-- The induced weight filtration is increasing. -/
theorem weightFiltration_mono : Monotone (A.weightFiltration w) :=
  fun _ _ h _ hf ↦ TauCeti.MvPolynomial.weightFiltration_mono h hf

/-- The induced filtration, with its strict lower stages, is a native ring filtration. -/
instance weightFiltrationIsRingFiltration :
    IsRingFiltration (A.weightFiltration w) (A.weightFiltrationLT w) where
  mono := A.weightFiltration_mono w
  is_le h _ hf := IsFiltration.is_le
    (F := TauCeti.MvPolynomial.weightFiltration R w) h hf
  is_sup B n hB := by
    cases n with
    | zero =>
      intro f hf
      have hf0 : (f : MvPolynomial σ R) = 0 := by
        simpa using (A.mem_weightFiltrationLT_iff w).mp hf
      have : f = 0 := Subtype.ext hf0
      exact this ▸ B.zero_mem
    | succ n =>
      intro f hf
      apply hB n (Nat.lt_succ_self n)
      simpa [weightFiltrationLT, weightFiltration,
        TauCeti.MvPolynomial.weightFiltrationLT_succ] using hf

/-- Every element of a polynomial subalgebra has a finite weight bound. -/
theorem iSup_weightFiltration : (⨆ n, A.weightFiltration w n) = ⊤ := by
  apply top_unique
  intro f _
  apply Submodule.mem_iSup_of_mem ((f : MvPolynomial σ R).weightedTotalDegree w)
  exact mem_weightFiltration_iff_weightedTotalDegree_le.mpr le_rfl

/-- The parameter belongs to the Rees algebra of the induced weight filtration. -/
theorem one_mem_weightFiltration_one : (1 : A) ∈ A.weightFiltration w 1 := by
  simpa using TauCeti.MvPolynomial.one_mem_weightFiltration_one R w

/-- The Rees algebra of the induced weight filtration, inside `A[t]`. -/
noncomputable abbrev weightReesAlgebra : Subalgebra R A[X] :=
  coeffSubalgebra (A.weightFiltration w)

/-- The induced weight Rees algebra is an algebra over the polynomial parameter ring `R[t]`. -/
noncomputable instance weightReesAlgebraAlgebra : Algebra R[X] (A.weightReesAlgebra w) :=
  coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)

/-- The parameter-ring algebra structure on `A.weightReesAlgebra w` extends the `R`-algebra
structure. -/
noncomputable instance weightReesAlgebraIsScalarTower :
    IsScalarTower R R[X] (A.weightReesAlgebra w) :=
  coeffSubalgebra.isScalarTower (A.weightFiltration w) (A.one_mem_weightFiltration_one w)

/-- The induced Rees algebra embeds as the intersection of the ambient weight Rees algebra
with the polynomial algebra having coefficients in `A`. -/
theorem map_weightReesAlgebra :
    (A.weightReesAlgebra w).map (Polynomial.mapAlgHom A.val) =
      TauCeti.MvPolynomial.weightReesAlgebra R w ⊓ (Polynomial.mapAlgHom A.val).range := by
  ext p
  simp only [Subalgebra.mem_map, Algebra.mem_inf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, AlgHom.mem_range_self _ q⟩
    rw [TauCeti.MvPolynomial.weightReesAlgebra, mem_coeffSubalgebra_iff]
    simpa using mem_coeffSubalgebra_iff.mp hq
  · rintro ⟨hp, q, rfl⟩
    refine ⟨q, ?_, rfl⟩
    apply mem_coeffSubalgebra_iff.mpr
    simpa using mem_coeffSubalgebra_iff.mp hp

/-- The canonical inclusion of the subalgebra weight Rees algebra into the ambient polynomial
weight Rees algebra, as an `R[t]`-algebra homomorphism. -/
noncomputable def weightReesInclusion :
    A.weightReesAlgebra w →ₐ[R[X]] TauCeti.MvPolynomial.weightReesAlgebra R w :=
  coeffSubalgebra.mapPolynomialAlgHom (A.weightFiltration w)
    (TauCeti.MvPolynomial.weightFiltration R w) A.val
    (fun _ _ hb ↦ by rw [Subalgebra.coe_val]; exact (A.mem_weightFiltration_iff w).mp hb)
    (A.one_mem_weightFiltration_one w) (TauCeti.MvPolynomial.one_mem_weightFiltration_one R w)

@[simp]
theorem coe_weightReesInclusion (g : A.weightReesAlgebra w) :
    (A.weightReesInclusion w g : (MvPolynomial σ R)[X]) = (g : A[X]).map A.val := by
  simp [weightReesInclusion]

theorem weightReesInclusion_injective : Function.Injective (A.weightReesInclusion w) :=
  coeffSubalgebra.mapPolynomialAlgHom_injective _ _ _ Subtype.val_injective

@[simp]
theorem weightReesInclusion_monomial {n : ℕ} {b : A} (hb : b ∈ A.weightFiltration w n) :
    A.weightReesInclusion w (coeffSubalgebra.monomial _ n b hb) =
      coeffSubalgebra.monomial _ n (b : MvPolynomial σ R)
        ((A.mem_weightFiltration_iff w).mp hb) := by
  simp [weightReesInclusion]

@[simp]
theorem weightReesInclusion_X :
    A.weightReesInclusion w (coeffSubalgebra.X _ (A.one_mem_weightFiltration_one w)) =
      coeffSubalgebra.X _ (TauCeti.MvPolynomial.one_mem_weightFiltration_one R w) := by
  simp [weightReesInclusion]

@[simp]
theorem eval_weightReesInclusion (r : R) (g : A.weightReesAlgebra w) :
    coeffSubalgebra.eval (TauCeti.MvPolynomial.weightFiltration R w) r (A.weightReesInclusion w g) =
      (coeffSubalgebra.eval (A.weightFiltration w) r g : MvPolynomial σ R) := by
  simp [weightReesInclusion]

@[simp]
theorem evalOne_weightReesInclusion (g : A.weightReesAlgebra w) :
    coeffSubalgebra.evalOne (TauCeti.MvPolynomial.weightFiltration R w)
      (A.weightReesInclusion w g) =
      (coeffSubalgebra.evalOne (A.weightFiltration w) g : MvPolynomial σ R) := by
  simp [weightReesInclusion]

end Subalgebra

namespace Subalgebra

variable {σ R : Type*} [CommSemiring R]

/-- Functoriality of the weight Rees algebra for an inclusion of subalgebras `A ≤ B`, as a map of
`R[t]`-algebras. -/
noncomputable def weightReesMap {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B) (w : σ → ℕ) :
    A.weightReesAlgebra w →ₐ[R[X]] B.weightReesAlgebra w :=
  coeffSubalgebra.mapPolynomialAlgHom (A.weightFiltration w) (B.weightFiltration w)
    (Subalgebra.inclusion h)
    (fun _ _ hb ↦ (B.mem_weightFiltration_iff w).mpr ((A.mem_weightFiltration_iff w).mp hb))
    (A.one_mem_weightFiltration_one w) (B.one_mem_weightFiltration_one w)

@[simp]
theorem coe_weightReesMap {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B) (w : σ → ℕ)
    (g : A.weightReesAlgebra w) :
    (weightReesMap h w g : B[X]) = (g : A[X]).map (Subalgebra.inclusion h) := by
  simp [weightReesMap]

@[simp]
theorem weightReesInclusion_weightReesMap {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B)
    (w : σ → ℕ) (g : A.weightReesAlgebra w) :
    B.weightReesInclusion w (weightReesMap h w g) = A.weightReesInclusion w g := by
  apply Subtype.ext
  ext n
  simp [weightReesInclusion, weightReesMap]

theorem weightReesMap_injective {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B) (w : σ → ℕ) :
    Function.Injective (weightReesMap h w) :=
  coeffSubalgebra.mapPolynomialAlgHom_injective _ _ _ (Subalgebra.inclusion_injective h)

@[simp]
theorem weightReesMap_monomial {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B) (w : σ → ℕ)
    {n : ℕ} {b : A} (hb : b ∈ A.weightFiltration w n) :
    weightReesMap h w (coeffSubalgebra.monomial _ n b hb) =
      coeffSubalgebra.monomial _ n (Subalgebra.inclusion h b)
        ((B.mem_weightFiltration_iff w).mpr ((A.mem_weightFiltration_iff w).mp hb)) := by
  simp [weightReesMap]

@[simp]
theorem weightReesMap_X {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B) (w : σ → ℕ) :
    weightReesMap h w (coeffSubalgebra.X _ (A.one_mem_weightFiltration_one w)) =
      coeffSubalgebra.X _ (B.one_mem_weightFiltration_one w) := by
  simp [weightReesMap]

@[simp]
theorem weightReesMap_refl (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ) :
    weightReesMap (le_refl A) w = AlgHom.id R[X] (A.weightReesAlgebra w) := by
  simp [weightReesMap]

@[simp]
theorem weightReesMap_weightReesMap {A B C : Subalgebra R (MvPolynomial σ R)}
    (hAB : A ≤ B) (hBC : B ≤ C) (w : σ → ℕ) (g : A.weightReesAlgebra w) :
    weightReesMap hBC w (weightReesMap hAB w g) = weightReesMap (hAB.trans hBC) w g := by
  apply Subtype.ext
  ext n
  simp [weightReesMap]

theorem weightReesMap_comp {A B C : Subalgebra R (MvPolynomial σ R)}
    (hAB : A ≤ B) (hBC : B ≤ C) (w : σ → ℕ) :
    (weightReesMap hBC w).comp (weightReesMap hAB w) = weightReesMap (hAB.trans hBC) w :=
  AlgHom.ext (weightReesMap_weightReesMap hAB hBC w)

@[simp]
theorem eval_weightReesMap {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B) (w : σ → ℕ)
    (r : R) (g : A.weightReesAlgebra w) :
    coeffSubalgebra.eval (B.weightFiltration w) r (weightReesMap h w g) =
      Subalgebra.inclusion h (coeffSubalgebra.eval (A.weightFiltration w) r g) := by
  simp [weightReesMap]

@[simp]
theorem evalOne_weightReesMap {A B : Subalgebra R (MvPolynomial σ R)} (h : A ≤ B) (w : σ → ℕ)
    (g : A.weightReesAlgebra w) :
    coeffSubalgebra.evalOne (B.weightFiltration w) (weightReesMap h w g) =
      Subalgebra.inclusion h (coeffSubalgebra.evalOne (A.weightFiltration w) g) := by
  simp [weightReesMap]

end Subalgebra

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial TauCeti

section ReesLift

attribute [local instance] Polynomial.algebra

variable {σ ι R : Type*} [CommSemiring R] {A : Subalgebra R (MvPolynomial σ R)}
  {w : σ → ℕ} {c : ι → MvPolynomial σ R} {d : ι → ℕ}
  (hcA : ∀ i, c i ∈ A) (hc : ∀ i, c i ∈ weightFiltration R w (d i))

/-- The `R`-algebra lift of `weightReesAeval c d` into `A.weightReesAlgebra w` when each `c i`
lies in `A` and has weight at most `d i`. -/
private noncomputable def weightReesAevalLiftAux :
    (MvPolynomial ι R)[X] →ₐ[R] A.weightReesAlgebra w :=
  Polynomial.aevalTower
    (aeval fun i ↦ coeffSubalgebra.monomial (A.weightFiltration w) (d i) ⟨c i, hcA i⟩
      ((A.mem_weightFiltration_iff w).mpr (hc i)))
    (coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w))

/-- When each `c i` belongs to `A` and has ambient weight at most `d i`, the Rees presentation map
`weightReesAeval c d` lifts to an `R[t]`-algebra homomorphism from `(MvPolynomial ι R)[t]` into
`A.weightReesAlgebra w`. -/
noncomputable def weightReesAevalLift : (MvPolynomial ι R)[X] →ₐ[R[X]] A.weightReesAlgebra w :=
  (weightReesAevalLiftAux hcA hc).toPolynomialAlgHom (by simp [weightReesAevalLiftAux])

@[simp]
theorem weightReesAevalLift_C {p : MvPolynomial ι R} :
    weightReesAevalLift hcA hc (Polynomial.C p) =
      aeval (fun i ↦ coeffSubalgebra.monomial (A.weightFiltration w) (d i) ⟨c i, hcA i⟩
        ((A.mem_weightFiltration_iff w).mpr (hc i))) p := by
  simp [weightReesAevalLift, weightReesAevalLiftAux]

@[simp]
theorem weightReesAevalLift_X :
    weightReesAevalLift hcA hc Polynomial.X =
      coeffSubalgebra.X (A.weightFiltration w) (A.one_mem_weightFiltration_one w) := by
  simp [weightReesAevalLift, weightReesAevalLiftAux]

/-- The lift `weightReesAevalLift hcA hc` composed with `A.weightReesInclusion w` and the ambient
subalgebra inclusion recovers `weightReesAeval c d` as an `R`-algebra homomorphism. -/
theorem val_comp_weightReesInclusion_comp_weightReesAevalLift :
    ((TauCeti.MvPolynomial.weightReesAlgebra R w).val.comp
        ((A.weightReesInclusion w).restrictScalars R)).comp
      ((weightReesAevalLift hcA hc).restrictScalars R) = weightReesAeval c d := by
  refine Polynomial.algHom_ext' (MvPolynomial.algHom_ext fun i ↦ ?_) ?_
  · simp [Polynomial.C_mul_X_pow_eq_monomial]
  · simp

theorem coe_weightReesInclusion_weightReesAevalLift (f : (MvPolynomial ι R)[X]) :
    (A.weightReesInclusion w (weightReesAevalLift hcA hc f) : (MvPolynomial σ R)[X]) =
      weightReesAeval c d f :=
  congr($(val_comp_weightReesInclusion_comp_weightReesAevalLift hcA hc) f)

@[simp]
theorem map_val_coe_weightReesAevalLift (f : (MvPolynomial ι R)[X]) :
    ((weightReesAevalLift hcA hc f : A.weightReesAlgebra w) : A[X]).map A.val =
      weightReesAeval c d f := by
  rw [← A.coe_weightReesInclusion w, coe_weightReesInclusion_weightReesAevalLift]

/-- On a polynomial `P` of weight at most `n`, `weightReesAevalLift` sends the homogenization of
`P` in degree `n` to `aeval c P * tⁿ` in `A.weightReesAlgebra w`. -/
theorem weightReesAevalLift_weightHomogenization {n : ℕ} {P : MvPolynomial ι R}
    (hP : P ∈ weightFiltration R d n) :
    weightReesAevalLift hcA hc (weightHomogenization R d n P) =
      coeffSubalgebra.monomial (A.weightFiltration w) n
        ⟨aeval c P, Algebra.adjoin_le (Set.range_subset_iff.mpr hcA)
          (by rw [← aeval_range]; exact ⟨P, rfl⟩)⟩
        ((A.mem_weightFiltration_iff w).mpr (aeval_mem_weightFiltration hc hP)) := by
  apply A.weightReesInclusion_injective w
  apply Subtype.ext
  rw [coe_weightReesInclusion_weightReesAevalLift, weightReesAeval_weightHomogenization hP,
    A.weightReesInclusion_monomial, coeffSubalgebra.coe_monomial]

@[simp]
theorem coe_eval_weightReesAevalLift (r : R) (f : (MvPolynomial ι R)[X]) :
    (coeffSubalgebra.eval (A.weightFiltration w) r (weightReesAevalLift hcA hc f) :
      MvPolynomial σ R) = (weightReesAeval c d f).eval (C r) := by
  rw [← A.eval_weightReesInclusion w r, coeffSubalgebra.eval_apply,
    coe_weightReesInclusion_weightReesAevalLift, MvPolynomial.algebraMap_eq]

@[simp]
theorem coe_evalOne_weightReesAevalLift (f : (MvPolynomial ι R)[X]) :
    (coeffSubalgebra.evalOne (A.weightFiltration w) (weightReesAevalLift hcA hc f) :
      MvPolynomial σ R) = aeval c (f.eval 1) := by
  rw [coeffSubalgebra.evalOne_eq_eval, coe_eval_weightReesAevalLift, map_one,
    eval_one_weightReesAeval]

/-- The kernel of `weightReesAevalLift hcA hc` equals the kernel of `weightReesAeval c d`. -/
theorem ker_weightReesAevalLift :
    RingHom.ker (weightReesAevalLift hcA hc) = RingHom.ker (weightReesAeval c d) := by
  have hinj : Function.Injective
      ((TauCeti.MvPolynomial.weightReesAlgebra R w).val.comp
        ((A.weightReesInclusion w).restrictScalars R)) :=
    Subtype.val_injective.comp (A.weightReesInclusion_injective w)
  ext f
  rw [RingHom.mem_ker, RingHom.mem_ker,
    ← val_comp_weightReesInclusion_comp_weightReesAevalLift hcA hc,
    AlgHom.comp_apply, map_eq_zero_iff _ hinj, AlgHom.restrictScalars_apply]

end ReesLift

end TauCeti.MvPolynomial

namespace Subalgebra

variable {σ R : Type*} [CommRing R] (A : Subalgebra R (MvPolynomial σ R)) (w : σ → ℕ)

/-- Over a commutative ring, the subalgebra weight Rees algebra is a commutative ring. -/
noncomputable instance weightReesAlgebraCommRing : CommRing (A.weightReesAlgebra w) :=
  letI : CommRing A := A.toCommRing
  @Subalgebra.toCommRing R A[X] _ _ _ (A.weightReesAlgebra w)

/-- The induced weight Rees algebra is flat over the actual parameter ring. No SAGBI basis,
finite generation, positivity of weights, or finite-variable hypothesis is needed. -/
theorem flat_weightReesAlgebra {k : Type*} [Field k]
    (A : Subalgebra k (MvPolynomial σ k)) (w : σ → ℕ) :
    letI := coeffSubalgebra.algebra (A.weightFiltration w) (A.one_mem_weightFiltration_one w)
    Module.Flat k[X] (A.weightReesAlgebra w) :=
  coeffSubalgebra.flat _ _

end Subalgebra
