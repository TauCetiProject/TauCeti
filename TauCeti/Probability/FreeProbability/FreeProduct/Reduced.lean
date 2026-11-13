/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.GNS.Uniqueness
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.StarAlgebra.GNS.Bounded
public import TauCeti.Probability.FreeProbability.FreeProduct.Positive
public import TauCeti.Probability.FreeProbability.Law.Basic
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Subalgebra
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Probability.FreeProbability.Orthogonality

/-!
# Reduced C⋆-free products of unital C⋆-algebras

Given a family of unital C⋆-algebras `A i` equipped with states `φ i : A i →ₚ[ℂ] ℂ` (`φ i 1 = 1`),
the algebraic free product expectation yields a normalized positive functional on
`LinearAlgebra.FreeProduct ℂ A`. For every positive functional `ψ` on
`LinearAlgebra.FreeProduct ℂ A` whose factors are unital C⋆-algebras, the C⋆-inequality
`a⋆ a ≤ ‖a‖² · 1` in each factor forces left multiplication by every element of
`LinearAlgebra.FreeProduct ℂ A` to be bounded on the GNS space `ψ.GNS`. Hence `ψ` admits a global
bounded GNS `⋆`-representation into `ψ.HilbertGNS →L[ℂ] ψ.HilbertGNS`.

Specializing to the free-product state `reducedFreeProductFunctional φ hφ` and taking the norm
closure of the image of its GNS representation produces a unital C⋆-algebra
`TauCeti.ReducedFreeProduct φ hφ`, the **reduced C⋆-free product** `⋆_{i} (A i, φ i)`. It comes
with:

* `TauCeti.ReducedFreeProduct.Hilbert φ hφ` — the GNS Hilbert space of the free-product state, with
  distinguished unit vacuum vector `TauCeti.ReducedFreeProduct.vacuum φ hφ`;
* `TauCeti.ReducedFreeProduct.of φ hφ` — the canonical unital `⋆`-homomorphism from the algebraic
  free product `LinearAlgebra.FreeProduct ℂ A`, with dense range;
* `TauCeti.ReducedFreeProduct.ι φ hφ i` — the canonical factor `⋆`-homomorphism from `A i` into
  `ReducedFreeProduct φ hφ`;
* `TauCeti.ReducedFreeProduct.state φ hφ` — the reduced free-product vacuum state, extending `φ i`
  along `ι φ hφ i` and making the factor images freely independent;
* exact identification of the kernel and norm of `ι φ hφ i` with the GNS representation of `φ i`,
  giving isometric factor embeddings whenever `(φ i).gnsStarAlgHom` is injective (in particular when
  `φ i` is faithful);
* preservation of spectral laws (`PositiveLinearMap.law`), traciality when all `φ i` are tracial,
  unitary equivalence with the GNS representation of `state φ hφ`, and identifications in the empty
  and singleton index cases.

No faithfulness or traciality of the factor states is required for the construction itself.
Note that faithfulness of `state φ hφ` on `ReducedFreeProduct φ hφ` is not asserted here.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §§1.4–1.5.
* D. Avitzour, *Free products of C*-algebras*, Trans. Amer. Math. Soc. **271** (1982), 423–435.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 5 and 7.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace CStarAlgebra
open LinearAlgebra.FreeProduct

namespace TauCeti

section GeneralBoundedness

variable {I : Type*} [DecidableEq I] {A : I → Type*} [∀ i, CStarAlgebra (A i)]

private theorem freeProduct_quadratic_bound
    (ψ : StarPositiveFunctional (LinearAlgebra.FreeProduct ℂ A)) (i : I) (a : A i)
    (b : LinearAlgebra.FreeProduct ℂ A) :
    ψ (star b * star (ι ℂ A i a) * ι ℂ A i a * b) ≤ (‖a‖ : ℂ) ^ 2 * ψ (star b * b) := by
  let := fun j => CStarAlgebra.spectralOrder (A j)
  have := fun j => CStarAlgebra.spectralOrderedRing (A j)
  have hle : star a * a ≤ algebraMap ℝ (A i) (‖a‖ ^ 2) :=
    CStarAlgebra.star_mul_le_algebraMap_norm_sq a
  have hdiff : 0 ≤ algebraMap ℝ (A i) (‖a‖ ^ 2) - star a * a := sub_nonneg.mpr hle
  set c : A i := CFC.sqrt (algebraMap ℝ (A i) (‖a‖ ^ 2) - star a * a)
  have hc : star c * c = algebraMap ℝ (A i) (‖a‖ ^ 2) - star a * a := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,
      CFC.sqrt_mul_sqrt_self _ hdiff]
  have hsum : star a * a + star c * c = ((‖a‖ : ℂ) ^ 2) • (1 : A i) := by
    rw [hc, add_sub_cancel, ← Algebra.algebraMap_eq_smul_one,
      IsScalarTower.algebraMap_apply ℝ ℂ (A i), Complex.coe_algebraMap, Complex.ofReal_pow]
  have himap := congrArg (ι ℂ A i) hsum
  simp only [map_add, map_mul, ← star_ι, map_smul, map_one] at himap
  have hconj : star b * star (ι ℂ A i a) * ι ℂ A i a * b +
      star (ι ℂ A i c * b) * (ι ℂ A i c * b) =
      ((‖a‖ : ℂ) ^ 2) • (star b * b) := by
    calc
      star b * star (ι ℂ A i a) * ι ℂ A i a * b +
          star (ι ℂ A i c * b) * (ι ℂ A i c * b)
          = star b * (star (ι ℂ A i a) * ι ℂ A i a + star (ι ℂ A i c) * ι ℂ A i c) * b := by
            simp only [star_mul, mul_assoc, mul_add, add_mul]
      _ = star b * (((‖a‖ : ℂ) ^ 2) • (1 : LinearAlgebra.FreeProduct ℂ A)) * b := by
            rw [himap]
      _ = ((‖a‖ : ℂ) ^ 2) • (star b * b) := by
            simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_one]
  have hψ := congrArg ψ hconj
  rw [map_add, map_smul, smul_eq_mul] at hψ
  calc
    ψ (star b * star (ι ℂ A i a) * ι ℂ A i a * b)
      ≤ ψ (star b * star (ι ℂ A i a) * ι ℂ A i a * b) +
          ψ (star (ι ℂ A i c * b) * (ι ℂ A i c * b)) :=
        le_add_of_nonneg_right (ψ.square_nonneg (ι ℂ A i c * b))
    _ = (‖a‖ : ℂ) ^ 2 * ψ (star b * b) := hψ

/-- Every positive functional on an algebraic free product of unital C⋆-algebras makes left
multiplication by each generator bounded on the algebraic GNS space. -/
theorem freeProduct_continuous_leftMul_ι
    (ψ : StarPositiveFunctional (LinearAlgebra.FreeProduct ℂ A)) (i : I) (a : A i) :
    Continuous (ψ.leftMul (ι ℂ A i a)) :=
  (ψ.continuous_leftMul_iff (ι ℂ A i a)).mpr
    ⟨‖a‖, norm_nonneg a, fun b => freeProduct_quadratic_bound ψ i a b⟩

/-- Every positive functional on an algebraic free product of unital C⋆-algebras makes left
multiplication by every element continuous on the algebraic GNS space. -/
theorem freeProduct_continuous_leftMul
    (ψ : StarPositiveFunctional (LinearAlgebra.FreeProduct ℂ A))
    (x : LinearAlgebra.FreeProduct ℂ A) :
    Continuous (ψ.leftMul x) := by
  rw [← ψ.mem_boundedSubalgebra]
  have htop : ψ.boundedSubalgebra = ⊤ := by
    rw [eq_top_iff, ← iSup_range_ιStar ℂ A]
    refine iSup_le ?_
    rintro i _ ⟨a, rfl⟩
    exact ψ.mem_boundedSubalgebra.mpr (by
      change Continuous (ψ.leftMul (ιStar ℂ A i a))
      rw [ιStar_apply]
      exact freeProduct_continuous_leftMul_ι ψ i a)
  exact htop.symm ▸ trivial

end GeneralBoundedness

section Construction

variable {I : Type*} [DecidableEq I] {A : I → Type*}
  [∀ i, CStarAlgebra (A i)] [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (φ : ∀ i, A i →ₚ[ℂ] ℂ) (hφ : ∀ i, φ i 1 = 1)

/-- The positive functional on `LinearAlgebra.FreeProduct ℂ A` induced by a family of states
`φ i : A i →ₚ[ℂ] ℂ`. -/
def reducedFreeProductFunctional :
    StarPositiveFunctional (LinearAlgebra.FreeProduct ℂ A) where
  toLinearMap := freeProductExpectation (fun i => (φ i).toLinearMap) hφ
  square_nonneg := freeProductExpectation_star_mul_self_nonneg _ hφ
    fun i a => (φ i).map_nonneg (star_mul_self_nonneg a)

theorem reducedFreeProductFunctional_apply (x : LinearAlgebra.FreeProduct ℂ A) :
    reducedFreeProductFunctional φ hφ x =
      freeProductExpectation (fun i => (φ i).toLinearMap) hφ x :=
  (rfl)

@[simp]
theorem reducedFreeProductFunctional_one : reducedFreeProductFunctional φ hφ 1 = 1 := by
  rw [reducedFreeProductFunctional_apply, freeProductExpectation_one]

@[simp]
theorem reducedFreeProductFunctional_ι (i : I) (a : A i) :
    reducedFreeProductFunctional φ hφ (ι ℂ A i a) = φ i a := by
  rw [reducedFreeProductFunctional_apply, freeProductExpectation_ι]
  rfl

/-- The GNS Hilbert space on which the reduced C⋆-free product acts faithfully. -/
abbrev ReducedFreeProduct.Hilbert (φ : ∀ i, A i →ₚ[ℂ] ℂ) (hφ : ∀ i, φ i 1 = 1) : Type _ :=
  (reducedFreeProductFunctional φ hφ).HilbertGNS

/-- The GNS representation of `LinearAlgebra.FreeProduct ℂ A` associated to `φ`. -/
def reducedFreeProductRep :
    LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ]
      (ReducedFreeProduct.Hilbert φ hφ →L[ℂ] ReducedFreeProduct.Hilbert φ hφ) :=
  (reducedFreeProductFunctional φ hφ).boundedRepresentation
    (freeProduct_continuous_leftMul (reducedFreeProductFunctional φ hφ))

private def starAlgHomRangeClosure {B H : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  π.range.topologicalClosure

private theorem mem_starAlgHomRangeClosure {B H : Type*} [Semiring B] [StarRing B] [Algebra ℂ B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (x : B) : π x ∈ starAlgHomRangeClosure π :=
  StarSubalgebra.le_topologicalClosure π.range ⟨x, rfl⟩

/-- The concrete C⋆-subalgebra of operators generated by the GNS representation of the free
product state. -/
def reducedFreeProductSubalgebra :
    StarSubalgebra ℂ
      (ReducedFreeProduct.Hilbert φ hφ →L[ℂ] ReducedFreeProduct.Hilbert φ hφ) :=
  starAlgHomRangeClosure (reducedFreeProductRep φ hφ)

instance :
    IsClosed
      (reducedFreeProductSubalgebra φ hφ :
        Set (ReducedFreeProduct.Hilbert φ hφ →L[ℂ] ReducedFreeProduct.Hilbert φ hφ)) :=
  isClosed_closure

/-- The **reduced C⋆-free product** `⋆_i (A i, φ i)` of unital C⋆-algebras `A i` equipped with
states `φ i`, realized as the norm closure of the algebraic free product in the GNS representation
of its free-product state. -/
def ReducedFreeProduct (φ : ∀ i, A i →ₚ[ℂ] ℂ) (hφ : ∀ i, φ i 1 = 1) : Type _ :=
  reducedFreeProductSubalgebra φ hφ

namespace ReducedFreeProduct

instance : CStarAlgebra (ReducedFreeProduct φ hφ) :=
  inferInstanceAs (CStarAlgebra (reducedFreeProductSubalgebra φ hφ))

instance : PartialOrder (ReducedFreeProduct φ hφ) :=
  CStarAlgebra.spectralOrder _

instance : StarOrderedRing (ReducedFreeProduct φ hφ) :=
  CStarAlgebra.spectralOrderedRing _

/-- The canonical isometric `⋆`-embedding of `ReducedFreeProduct φ hφ` as bounded operators on
`Hilbert φ hφ`. -/
def toOperator : ReducedFreeProduct φ hφ →⋆ₐ[ℂ] (Hilbert φ hφ →L[ℂ] Hilbert φ hφ) where
  toFun x := x.1
  map_one' := (rfl)
  map_mul' _ _ := (rfl)
  map_zero' := (rfl)
  map_add' _ _ := (rfl)
  commutes' _ := (rfl)
  map_star' _ := (rfl)

theorem toOperator_injective : Function.Injective (toOperator φ hφ) :=
  Subtype.val_injective

theorem isometry_toOperator : Isometry (toOperator φ hφ) :=
  NonUnitalStarAlgHom.isometry (toOperator φ hφ) (toOperator_injective φ hφ)

@[simp]
theorem norm_toOperator (x : ReducedFreeProduct φ hφ) : ‖toOperator φ hφ x‖ = ‖x‖ :=
  (rfl)

/-- The canonical unital `⋆`-homomorphism from the algebraic free product
`LinearAlgebra.FreeProduct ℂ A` into `ReducedFreeProduct φ hφ`. -/
def of : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] ReducedFreeProduct φ hφ where
  toFun x :=
    ⟨reducedFreeProductRep φ hφ x, mem_starAlgHomRangeClosure (reducedFreeProductRep φ hφ) x⟩
  map_one' := Subtype.ext (map_one (reducedFreeProductRep φ hφ))
  map_mul' x y := Subtype.ext (map_mul (reducedFreeProductRep φ hφ) x y)
  map_zero' := Subtype.ext (map_zero (reducedFreeProductRep φ hφ))
  map_add' x y := Subtype.ext (map_add (reducedFreeProductRep φ hφ) x y)
  commutes' r := Subtype.ext ((reducedFreeProductRep φ hφ).commutes r)
  map_star' x := Subtype.ext (map_star (reducedFreeProductRep φ hφ) x)

@[simp]
theorem toOperator_of (x : LinearAlgebra.FreeProduct ℂ A) :
    toOperator φ hφ (of φ hφ x) = reducedFreeProductRep φ hφ x :=
  (rfl)

/-- The canonical unital `⋆`-homomorphism from the factor `A i` into `ReducedFreeProduct φ hφ`. -/
def ι (i : I) : A i →⋆ₐ[ℂ] ReducedFreeProduct φ hφ :=
  (of φ hφ).comp (ιStar ℂ A i)

@[simp]
theorem of_ι (i : I) (a : A i) :
    of φ hφ (LinearAlgebra.FreeProduct.ι ℂ A i a) = ι φ hφ i a := by
  simp only [ι, StarAlgHom.comp_apply, ιStar_apply]

@[simp]
theorem toOperator_ι (i : I) (a : A i) :
    toOperator φ hφ (ι φ hφ i a) =
      reducedFreeProductRep φ hφ (LinearAlgebra.FreeProduct.ι ℂ A i a) := by
  rw [← of_ι, toOperator_of]

theorem norm_ι_le (i : I) (a : A i) : ‖ι φ hφ i a‖ ≤ ‖a‖ :=
  NonUnitalStarAlgHom.norm_apply_le (ι φ hφ i) a

/-- The algebraic free product maps densely into the reduced C⋆-free product. -/
theorem denseRange_of : DenseRange (of φ hφ) := by
  let T := reducedFreeProductRep φ hφ
  have hd : DenseRange (Set.inclusion (s := Set.range T) subset_closure) :=
    (denseRange_inclusion_iff subset_closure).2 subset_rfl
  exact hd.comp Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

/-- Closed predicates on `ReducedFreeProduct φ hφ` can be verified on the image of
`LinearAlgebra.FreeProduct ℂ A`. -/
@[elab_as_elim]
theorem induction_on {p : ReducedFreeProduct φ hφ → Prop} (x : ReducedFreeProduct φ hφ)
    (hp : IsClosed {x | p x}) (ih : ∀ y : LinearAlgebra.FreeProduct ℂ A, p (of φ hφ y)) : p x :=
  (denseRange_of φ hφ).induction (by rintro _ ⟨y, rfl⟩; exact ih y) hp x

/-- Unital `⋆`-homomorphisms out of `ReducedFreeProduct φ hφ` into a C⋆-algebra are determined on
the factor embeddings `ι φ hφ i`. -/
@[ext]
theorem starAlgHom_ext {B : Type*} [CStarAlgebra B]
    {f g : ReducedFreeProduct φ hφ →⋆ₐ[ℂ] B}
    (h : ∀ i a, f (ι φ hφ i a) = g (ι φ hφ i a)) : f = g := by
  refine StarAlgHom.ext fun x => induction_on φ hφ x
    (isClosed_eq (map_continuous f) (map_continuous g)) ?_
  have hof : f.comp (of φ hφ) = g.comp (of φ hφ) := by
    ext i a
    change f (of φ hφ (LinearAlgebra.FreeProduct.ι ℂ A i a)) =
      g (of φ hφ (LinearAlgebra.FreeProduct.ι ℂ A i a))
    simpa only [of_ι] using h i a
  exact fun y => DFunLike.congr_fun hof y

/-- The factor C⋆-subalgebras `(ι φ hφ i).range` topologically generate `ReducedFreeProduct φ hφ`.
-/
theorem topologicalClosure_iSup_range_ι :
    (⨆ i, (ι φ hφ i).range).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine induction_on φ hφ x (StarSubalgebra.isClosed_topologicalClosure _) fun y => ?_
  have hle : (⨆ i, (ιStar ℂ A i).range : StarSubalgebra ℂ (LinearAlgebra.FreeProduct ℂ A)) ≤
      (⨆ i, (ι φ hφ i).range).comap (of φ hφ) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨a, rfl⟩
    exact le_iSup (fun j => (ι φ hφ j).range) i ⟨a, rfl⟩
  rw [iSup_range_ιStar ℂ A, top_le_iff] at hle
  have hy : y ∈ (⨆ i, (ι φ hφ i).range).comap (of φ hφ) := hle.symm ▸ trivial
  exact StarSubalgebra.le_topologicalClosure _ hy

/-! ### The vacuum vector and reduced free-product state -/

/-- The canonical vacuum vector in `Hilbert φ hφ`. -/
def vacuum (φ : ∀ i, A i →ₚ[ℂ] ℂ) (hφ : ∀ i, φ i 1 = 1) : Hilbert φ hφ :=
  (reducedFreeProductFunctional φ hφ).hilbertCyclicVector

theorem vacuum_def :
    vacuum φ hφ = (reducedFreeProductFunctional φ hφ).hilbertCyclicVector :=
  (rfl)

/-- The vacuum vector is a unit vector. -/
@[simp]
theorem norm_vacuum : ‖vacuum φ hφ‖ = 1 :=
  (reducedFreeProductFunctional φ hφ).norm_hilbertCyclicVector
    (reducedFreeProductFunctional_one φ hφ)

/-- The vacuum vector is cyclic for `ReducedFreeProduct φ hφ`. -/
theorem denseRange_toOperator_vacuum :
    DenseRange (fun x : ReducedFreeProduct φ hφ => toOperator φ hφ x (vacuum φ hφ)) := by
  have hd : DenseRange
      ((fun x : ReducedFreeProduct φ hφ => toOperator φ hφ x (vacuum φ hφ)) ∘ of φ hφ) := by
    simpa only [Function.comp_def, toOperator_of, reducedFreeProductRep, vacuum_def] using
      (reducedFreeProductFunctional φ hφ).denseRange_boundedRepresentation_hilbertCyclicVector
        (freeProduct_continuous_leftMul _)
  exact hd.of_comp

private theorem toOperator_nonneg {x : ReducedFreeProduct φ hφ} (hx : 0 ≤ x) :
    0 ≤ toOperator φ hφ x := by
  have hsqrt : x = star (CFC.sqrt x) * CFC.sqrt x := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq, CFC.sqrt_mul_sqrt_self x hx]
  rw [hsqrt, map_mul, map_star]
  exact star_mul_self_nonneg (toOperator φ hφ (CFC.sqrt x))

/-- The reduced free-product vacuum state on `ReducedFreeProduct φ hφ`. -/
def state (φ : ∀ i, A i →ₚ[ℂ] ℂ) (hφ : ∀ i, φ i 1 = 1) :
    ReducedFreeProduct φ hφ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((reducedFreeProductFunctional φ hφ).hilbertPositiveLinearMap.toLinearMap.comp
      (toOperator φ hφ).toLinearMap)
    fun _ hx => (reducedFreeProductFunctional φ hφ).hilbertPositiveLinearMap.map_nonneg
      (toOperator_nonneg φ hφ hx)

theorem state_apply (x : ReducedFreeProduct φ hφ) :
    state φ hφ x = ⟪vacuum φ hφ, toOperator φ hφ x (vacuum φ hφ)⟫_ℂ :=
  (reducedFreeProductFunctional φ hφ).hilbertPositiveLinearMap_apply (toOperator φ hφ x)

@[simp]
theorem state_one : state φ hφ 1 = 1 := by
  simp [state_apply, vacuum_def]

instance : Nontrivial (ReducedFreeProduct φ hφ) :=
  ⟨⟨1, 0, fun h => by
    have := congrArg (state φ hφ) h
    simp at this⟩⟩

@[simp]
theorem state_of (x : LinearAlgebra.FreeProduct ℂ A) :
    state φ hφ (of φ hφ x) = freeProductExpectation (fun i => (φ i).toLinearMap) hφ x := by
  rw [state_apply, toOperator_of, reducedFreeProductRep, vacuum_def,
    ← (reducedFreeProductFunctional φ hφ).hilbertPositiveLinearMap_apply,
    (reducedFreeProductFunctional φ hφ).hilbertPositiveLinearMap_boundedRepresentation]
  rfl

@[simp]
theorem state_ι (i : I) (a : A i) : state φ hφ (ι φ hφ i a) = φ i a := by
  rw [← of_ι, state_of, freeProductExpectation_ι]
  rfl

@[simp]
theorem state_comp_ι (i : I) :
    (state φ hφ).toLinearMap.comp (ι φ hφ i).toLinearMap = (φ i).toLinearMap := by
  ext a
  simp

/-! ### Free independence, joint distributions, spectral laws, and traciality -/

/-- The canonical factor subalgebras `(ι φ hφ i).range` are freely independent in
`ReducedFreeProduct φ hφ` with respect to `state φ hφ`. -/
theorem isFreelyIndependent_state :
    IsFreelyIndependent (state φ hφ).toLinearMap fun i => (ι φ hφ i).range.toSubalgebra := by
  have hfree :
      IsFreelyIndependent (state φ hφ).toLinearMap
        fun i => (LinearAlgebra.FreeProduct.ι ℂ A i).range.map (of φ hφ).toAlgHom := by
    refine (isFreelyIndependent_freeProductExpectation
      (fun i => (φ i).toLinearMap) hφ).map (of φ hφ).toAlgHom ?_
    ext x
    simp
  have hrange : ∀ i,
      (LinearAlgebra.FreeProduct.ι ℂ A i).range.map (of φ hφ).toAlgHom =
        (ι φ hφ i).range.toSubalgebra := fun i => by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, (of_ι φ hφ i a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨LinearAlgebra.FreeProduct.ι ℂ A i a, ⟨a, rfl⟩, of_ι φ hφ i a⟩
  simpa only [hrange] using hfree

/-- Any choice of one element from each factor embeds as a freely independent family in
`ReducedFreeProduct φ hφ`. -/
theorem isFreelyIndependentElements_ι (a : ∀ i, A i) :
    IsFreelyIndependentElements (state φ hφ).toLinearMap fun i => ι φ hφ i (a i) := by
  rw [isFreelyIndependentElements_iff]
  exact (isFreelyIndependent_state φ hφ).mono fun i =>
    Algebra.adjoin_le <|
      Set.singleton_subset_iff.2 (AlgHom.mem_range_self (ι φ hφ i).toAlgHom (a i))

/-- Any choice of one element from each factor embeds as a star-freely independent family in
`ReducedFreeProduct φ hφ`. -/
theorem isStarFreelyIndependentElements_ι (a : ∀ i, A i) :
    IsStarFreelyIndependentElements (state φ hφ).toLinearMap fun i => ι φ hφ i (a i) := by
  rw [isStarFreelyIndependentElements_iff]
  refine (isFreelyIndependent_state φ hφ).mono fun i => ?_
  rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, ← map_star]
  refine Algebra.adjoin_le ?_
  rintro _ (rfl | rfl)
  · exact AlgHom.mem_range_self (ι φ hφ i).toAlgHom (a i)
  · exact AlgHom.mem_range_self (ι φ hφ i).toAlgHom (star (a i))

/-- Embedding a family of elements from factor `i` preserves their joint algebraic distribution. -/
theorem jointDistribution_state_comp_ι {κ : Type*} (i : I) (f : κ → A i) :
    jointDistribution (state φ hφ).toLinearMap (fun k => ι φ hφ i (f k)) =
      jointDistribution (φ i).toLinearMap f := by
  simpa [Function.comp_def] using
    (jointDistribution_map (state φ hφ).toLinearMap (ι φ hφ i).toAlgHom f).symm

/-- Embedding a family of elements from factor `i` preserves their joint star distribution. -/
theorem starDistribution_state_comp_ι {κ : Type*} (i : I) (f : κ → A i) :
    starDistribution (state φ hφ).toLinearMap (fun k => ι φ hφ i (f k)) =
      starDistribution (φ i).toLinearMap f := by
  simpa [Function.comp_def] using
    (starDistribution_map (state φ hφ).toLinearMap (ι φ hφ i) f).symm

/-- Embedding a selfadjoint element from factor `i` preserves its spectral law. -/
@[simp]
theorem law_ι {i : I} {a : A i} (ha : IsSelfAdjoint a) :
    PositiveLinearMap.law (state φ hφ) (ι φ hφ i a) = PositiveLinearMap.law (φ i) a := by
  rw [PositiveLinearMap.law_eq_law_iff_forall_apply_pow (state φ hφ) (φ i)
    (ha.map (ι φ hφ i)) ha]
  intro n
  rw [← map_pow, state_ι]

/-- **Traciality of the reduced free-product state.** If every factor state `φ i` is tracial,
then `state φ hφ` is tracial on `ReducedFreeProduct φ hφ`. -/
theorem state_mul_comm (htr : ∀ i (a b : A i), φ i (a * b) = φ i (b * a))
    (x y : ReducedFreeProduct φ hφ) : state φ hφ (x * y) = state φ hφ (y * x) := by
  refine induction_on φ hφ x
    (isClosed_eq ((map_continuous (state φ hφ)).comp (continuous_mul_const y))
      ((map_continuous (state φ hφ)).comp (continuous_const_mul y))) fun u => ?_
  refine induction_on φ hφ y
    (isClosed_eq ((map_continuous (state φ hφ)).comp (continuous_const_mul (of φ hφ u)))
      ((map_continuous (state φ hφ)).comp (continuous_mul_const (of φ hφ u)))) fun v => ?_
  simp only [← map_mul, state_of]
  exact freeProductExpectation_mul_comm (fun i => (φ i).toLinearMap) hφ htr u v

/-! ### Kernels, norms, and faithfulness of factor embeddings -/

private theorem freeProductExpectation_star_ι_mul_wordMul_eq_zero
    {i : I} {a : A i} (ha : ∀ b : A i, φ i (star (a * b) * (a * b)) = 0)
    (w : ReducedWord I) (m : ∀ k, WordTensorFactor (fun j => (φ j).toLinearMap) w k) :
    freeProductExpectation (fun j => (φ j).toLinearMap) hφ
      (star (LinearAlgebra.FreeProduct.ι ℂ A i a *
          wordMul (fun j => (φ j).toLinearMap) w (PiTensorProduct.tprod ℂ m)) *
        (LinearAlgebra.FreeProduct.ι ℂ A i a *
          wordMul (fun j => (φ j).toLinearMap) w (PiTensorProduct.tprod ℂ m))) = 0 := by
  have ha0 : φ i (star a * a) = 0 := by simpa only [mul_one] using ha 1
  have ha_mul : ∀ b : A i, φ i (a * b) = 0 := fun b => by
    have hcs := (StarPositiveFunctional.ofPositiveLinearMap (φ i)).apply_star_mul_self_eq_zero_iff
      (a * b) |>.mp (by simpa only [StarPositiveFunctional.ofPositiveLinearMap_apply] using ha b) 1
    simpa only [star_one, one_mul, StarPositiveFunctional.ofPositiveLinearMap_apply] using hcs
  have ha_val : φ i a = 0 := by simpa only [mul_one] using ha_mul 1
  have hfree : IsFreelyIndependent (freeProductExpectation (fun j => (φ j).toLinearMap) hφ)
      fun j => (ιStar ℂ A j).range.toSubalgebra := by
    simpa only [StarAlgHom.range, ιStar_toAlgHom] using
      isFreelyIndependent_freeProductExpectation (fun j => (φ j).toLinearMap) hφ
  obtain ⟨_ | ⟨j, rest⟩, hl⟩ := w
  · have hnil : wordMul (fun j => (φ j).toLinearMap) ⟨[], hl⟩ (PiTensorProduct.tprod ℂ m) = 1 := by
      rw [wordMul_nil, wordTensorNilEquiv_tprod, map_one]
    rw [hnil, mul_one, star_ι, ← map_mul, freeProductExpectation_ι]
    exact ha0
  · by_cases hji : j = i
    · subst j
      let m0 : A i := (m 0).1
      let V : List (I × LinearAlgebra.FreeProduct ℂ A) :=
        List.ofFn fun k : Fin rest.length =>
          (rest[k], LinearAlgebra.FreeProduct.ι ℂ A rest[k] (m k.succ).1)
      let W : List (I × LinearAlgebra.FreeProduct ℂ A) :=
        (i, LinearAlgebra.FreeProduct.ι ℂ A i (a * m0)) :: V
      have hW_fst : W.map Prod.fst = i :: rest := by
        simp [W, V, List.map_ofFn, Function.comp_def]
      have hW_prod : LinearAlgebra.FreeProduct.ι ℂ A i a *
          wordMul (fun k => (φ k).toLinearMap) ⟨i :: rest, hl⟩ (PiTensorProduct.tprod ℂ m) =
          (W.map Prod.snd).prod := by
        rw [wordMul_tprod, List.ofFn_succ, List.prod_cons]
        change LinearAlgebra.FreeProduct.ι ℂ A i a * (LinearAlgebra.FreeProduct.ι ℂ A i m0 *
          (List.ofFn fun k : Fin rest.length =>
            LinearAlgebra.FreeProduct.ι ℂ A rest[k] (m k.succ).1).prod) = _
        rw [← mul_assoc, ← map_mul]
        simp [W, V, List.map_ofFn, Function.comp_def]
      have hfree_app := hfree.apply_star_prod_mul_prod
        (freeProductExpectation_one _ hφ)
        (freeProductExpectation_star _ hφ fun k c => map_star (φ k) c)
        W W (hW_fst ▸ hl) (hW_fst ▸ hl)
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · exact ⟨a * m0, ιStar_apply ℂ A _ _⟩
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            exact ⟨(m k.succ).1, ιStar_apply ℂ A _ _⟩)
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · exact ⟨a * m0, ιStar_apply ℂ A _ _⟩
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            exact ⟨(m k.succ).1, ιStar_apply ℂ A _ _⟩)
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · rw [freeProductExpectation_ι]
            exact ha_mul m0
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            rw [freeProductExpectation_ι]
            exact LinearMap.mem_ker.mp (m k.succ).2)
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · rw [freeProductExpectation_ι]
            exact ha_mul m0
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            rw [freeProductExpectation_ι]
            exact LinearMap.mem_ker.mp (m k.succ).2)
      rw [hW_prod, hfree_app]
      simp only [W, ↓reduceIte, List.zipWith_cons_cons, List.prod_cons, star_ι, ← map_mul,
        freeProductExpectation_ι]
      change φ i (star (a * m0) * (a * m0)) * _ = 0
      rw [ha m0, zero_mul]
    · let V : List (I × LinearAlgebra.FreeProduct ℂ A) :=
        List.ofFn fun k : Fin (j :: rest).length =>
          ((j :: rest)[k], LinearAlgebra.FreeProduct.ι ℂ A (j :: rest)[k] (m k).1)
      let W : List (I × LinearAlgebra.FreeProduct ℂ A) :=
        (i, LinearAlgebra.FreeProduct.ι ℂ A i a) :: V
      have hV_fst : V.map Prod.fst = j :: rest := by
        simp [V, List.map_ofFn, Function.comp_def]
      have hW_chain : (W.map Prod.fst).IsChain (· ≠ ·) := by
        simp only [W, List.map_cons, hV_fst]
        exact List.isChain_cons.2
          ⟨fun k hk hik => by
            simp only [List.head?_cons, Option.mem_some_iff] at hk
            exact hji (hk ▸ hik.symm),
           hl⟩
      have hW_prod : LinearAlgebra.FreeProduct.ι ℂ A i a *
          wordMul (fun k => (φ k).toLinearMap) ⟨j :: rest, hl⟩ (PiTensorProduct.tprod ℂ m) =
          (W.map Prod.snd).prod := by
        rw [wordMul_tprod]
        simp [W, V, List.map_ofFn, Function.comp_def]
      have hfree_app := hfree.apply_star_prod_mul_prod
        (freeProductExpectation_one _ hφ)
        (freeProductExpectation_star _ hφ fun k c => map_star (φ k) c)
        W W hW_chain hW_chain
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · exact ⟨a, ιStar_apply ℂ A _ _⟩
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            exact ⟨(m k).1, ιStar_apply ℂ A _ _⟩)
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · exact ⟨a, ιStar_apply ℂ A _ _⟩
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            exact ⟨(m k).1, ιStar_apply ℂ A _ _⟩)
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · rw [freeProductExpectation_ι]
            exact ha_val
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            rw [freeProductExpectation_ι]
            exact LinearMap.mem_ker.mp (m k).2)
        (by
          simp only [W, List.mem_cons]
          rintro x (rfl | hx)
          · rw [freeProductExpectation_ι]
            exact ha_val
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            rw [freeProductExpectation_ι]
            exact LinearMap.mem_ker.mp (m k).2)
      rw [hW_prod, hfree_app]
      simp only [W, ↓reduceIte, List.zipWith_cons_cons, List.prod_cons, star_ι, ← map_mul,
        freeProductExpectation_ι]
      change φ i (star a * a) * _ = 0
      rw [ha0, zero_mul]

/-- An element of `A i` vanishes in the reduced C⋆-free product precisely when it lies in the
kernel of the GNS representation of `φ i`. -/
theorem ι_eq_zero_iff (i : I) (a : A i) :
    ι φ hφ i a = 0 ↔ ∀ b : A i, φ i (star (a * b) * (a * b)) = 0 := by
  classical
  constructor
  · intro h b
    have hmul : ι φ hφ i a * ι φ hφ i b = 0 := by rw [h, zero_mul]
    have hsq := congrArg (fun x => state φ hφ (star x * x)) hmul
    simpa only [← map_mul, ← map_star, state_ι, star_zero, mul_zero, map_zero] using hsq
  · intro ha
    apply toOperator_injective φ hφ
    rw [map_zero]
    refine (reducedFreeProductFunctional φ hφ).hilbertClassMap_clm_ext fun z => ?_
    rw [toOperator_ι, reducedFreeProductRep,
      (reducedFreeProductFunctional φ hφ).boundedRepresentation_hilbertClassMap, zero_apply]
    let d := equivReducedWords (fun j => (φ j).toLinearMap) hφ z
    have hz : z = ∑ w ∈ d.support, wordMul (fun j => (φ j).toLinearMap) w (d w) := by
      calc
        z = (equivReducedWords (fun j => (φ j).toLinearMap) hφ).symm d :=
          ((equivReducedWords _ hφ).symm_apply_apply z).symm
        _ = (equivReducedWords (fun j => (φ j).toLinearMap) hφ).symm
            (∑ w ∈ d.support, DirectSum.of _ w (d w)) := by
          rw [DirectSum.sum_support_of]
        _ = _ := by
          simp only [map_sum, ← DirectSum.lof_eq_of ℂ, equivReducedWords_symm_apply,
            reducedWordsToFreeProduct_lof]
    rw [hz, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    induction d w using PiTensorProduct.induction_on with
    | smul_tprod r m =>
      rw [map_smul (wordMul _ w), Algebra.mul_smul_comm, map_smul]
      suffices (reducedFreeProductFunctional φ hφ).hilbertClassMap
          (LinearAlgebra.FreeProduct.ι ℂ A i a *
            wordMul (fun j => (φ j).toLinearMap) w (PiTensorProduct.tprod ℂ m)) = 0 by
        rw [this, smul_zero]
      rw [(reducedFreeProductFunctional φ hφ).hilbertClassMap_eq_zero_iff,
        reducedFreeProductFunctional_apply,
        freeProductExpectation_star_ι_mul_wordMul_eq_zero φ hφ ha w m]
    | add x y hx hy =>
      rw [map_add (wordMul _ w), mul_add, map_add, hx, hy, add_zero]

/-- An element of `A i` maps to zero in `ReducedFreeProduct φ hφ` if and only if it maps to
zero in the GNS representation of `φ i`. -/
theorem ι_eq_zero_iff_gnsStarAlgHom (i : I) (a : A i) :
    ι φ hφ i a = 0 ↔ (φ i).gnsStarAlgHom a = 0 := by
  rw [ι_eq_zero_iff]
  constructor
  · intro ha
    refine DFunLike.coe_injective <| (φ i).denseRange_toGNS.equalizer
      ((φ i).gnsStarAlgHom a).continuous continuous_zero (funext fun b => ?_)
    have hact : (φ i).gnsStarAlgHom a ((φ i).toGNS b) = (φ i).toGNS (a * b) := by
      simp [PositiveLinearMap.gnsStarAlgHom_apply, PositiveLinearMap.toGNS_apply,
        PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
    dsimp
    rw [hact, zero_apply, PositiveLinearMap.toGNS_eq_zero_iff]
    exact ha b
  · intro ha b
    have hact : (φ i).gnsStarAlgHom a ((φ i).toGNS b) = (φ i).toGNS (a * b) := by
      simp [PositiveLinearMap.gnsStarAlgHom_apply, PositiveLinearMap.toGNS_apply,
        PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
    have hzero : (φ i).toGNS (a * b) = 0 := by
      simp only [← hact, ha, zero_apply]
    exact (PositiveLinearMap.toGNS_eq_zero_iff (φ i) (a * b)).mp hzero

/-- The kernel of `ι φ hφ i` coincides with the kernel of the GNS representation of `φ i`. -/
theorem ker_ι (i : I) :
    TwoSidedIdeal.ker (ι φ hφ i) = TwoSidedIdeal.ker (φ i).gnsStarAlgHom := by
  ext a
  simp only [TwoSidedIdeal.mem_ker]
  exact ι_eq_zero_iff_gnsStarAlgHom φ hφ i a

private theorem map_eq_of_ker_iff {B C D : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    [Ring C] [StarRing C] [Algebra ℂ C] [Ring D] [StarRing D] [Algebra ℂ D]
    (f : B →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] D) (hfg : ∀ x, f x = 0 → g x = 0)
    {x₁ x₂ : B} (h : f x₁ = f x₂) : g x₁ = g x₂ :=
  sub_eq_zero.mp <| (map_sub g _ _).symm.trans <| hfg _ <| (map_sub f _ _).trans (sub_eq_zero.mpr h)

private def rangeEquivOfKerIff {B C D : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    [Ring C] [StarRing C] [Algebra ℂ C] [StarModule ℂ C]
    [Ring D] [StarRing D] [Algebra ℂ D] [StarModule ℂ D]
    (f : B →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] D) (hfg : ∀ x, f x = 0 ↔ g x = 0) :
    f.range ≃⋆ₐ[ℂ] g.range where
  toFun y := g.rangeRestrict y.2.choose
  invFun z := f.rangeRestrict z.2.choose
  left_inv y := Subtype.ext <|
    (map_eq_of_ker_iff g f (fun _ hx => (hfg _).mpr hx)
      (g.rangeRestrict y.2.choose).2.choose_spec).trans y.2.choose_spec
  right_inv z := Subtype.ext <|
    (map_eq_of_ker_iff f g (fun _ hx => (hfg _).mp hx)
      (f.rangeRestrict z.2.choose).2.choose_spec).trans z.2.choose_spec
  map_mul' y₁ y₂ := Subtype.ext <| by
    change g (y₁ * y₂).2.choose = g y₁.2.choose * g y₂.2.choose
    rw [← map_mul]
    refine map_eq_of_ker_iff f g (fun _ hx => (hfg _).mp hx) ?_
    have h12 : f (y₁ * y₂).2.choose = (y₁ * y₂).1 := (y₁ * y₂).2.choose_spec
    have h1 : f y₁.2.choose = y₁.1 := y₁.2.choose_spec
    have h2 : f y₂.2.choose = y₂.1 := y₂.2.choose_spec
    rw [map_mul, h12, h1, h2]
    rfl
  map_add' y₁ y₂ := Subtype.ext <| by
    change g (y₁ + y₂).2.choose = g y₁.2.choose + g y₂.2.choose
    rw [← map_add]
    refine map_eq_of_ker_iff f g (fun _ hx => (hfg _).mp hx) ?_
    have h12 : f (y₁ + y₂).2.choose = (y₁ + y₂).1 := (y₁ + y₂).2.choose_spec
    have h1 : f y₁.2.choose = y₁.1 := y₁.2.choose_spec
    have h2 : f y₂.2.choose = y₂.1 := y₂.2.choose_spec
    rw [map_add, h12, h1, h2]
    rfl
  map_smul' c y := Subtype.ext <| by
    change g (c • y).2.choose = c • g y.2.choose
    rw [← map_smul]
    refine map_eq_of_ker_iff f g (fun _ hx => (hfg _).mp hx) ?_
    have hcy : f (c • y).2.choose = (c • y).1 := (c • y).2.choose_spec
    have hy : f y.2.choose = y.1 := y.2.choose_spec
    rw [map_smul, hcy, hy]
    rfl
  map_star' y := Subtype.ext <| by
    change g (star y).2.choose = star (g y.2.choose)
    rw [← map_star]
    refine map_eq_of_ker_iff f g (fun _ hx => (hfg _).mp hx) ?_
    have hsy : f (star y).2.choose = (star y).1 := (star y).2.choose_spec
    have hy : f y.2.choose = y.1 := y.2.choose_spec
    rw [map_star, hsy, hy]
    rfl

private theorem rangeEquivOfKerIff_rangeRestrict {B C D : Type*} [Ring B] [StarRing B]
    [Algebra ℂ B] [Ring C] [StarRing C] [Algebra ℂ C] [StarModule ℂ C]
    [Ring D] [StarRing D] [Algebra ℂ D] [StarModule ℂ D]
    (f : B →⋆ₐ[ℂ] C) (g : B →⋆ₐ[ℂ] D) (hfg : ∀ x, f x = 0 ↔ g x = 0) (a : B) :
    rangeEquivOfKerIff f g hfg (f.rangeRestrict a) = g.rangeRestrict a :=
  Subtype.ext <| map_eq_of_ker_iff f g (fun _ hx => (hfg _).mp hx) (f.rangeRestrict a).2.choose_spec

/-- The image of `A i` inside `ReducedFreeProduct φ hφ` is canonically `⋆`-isomorphic (hence
isometric) to its GNS representation range. -/
def factorRangeEquiv (i : I) : (ι φ hφ i).range ≃⋆ₐ[ℂ] (φ i).gnsStarAlgHom.range :=
  rangeEquivOfKerIff (ι φ hφ i) (φ i).gnsStarAlgHom (ι_eq_zero_iff_gnsStarAlgHom φ hφ i)

@[simp]
theorem factorRangeEquiv_rangeRestrict (i : I) (a : A i) :
    factorRangeEquiv φ hφ i ((ι φ hφ i).rangeRestrict a) =
      (φ i).gnsStarAlgHom.rangeRestrict a :=
  rangeEquivOfKerIff_rangeRestrict _ _ (ι_eq_zero_iff_gnsStarAlgHom φ hφ i) a

theorem coe_factorRangeEquiv_rangeRestrict (i : I) (a : A i) :
    (factorRangeEquiv φ hφ i ((ι φ hφ i).rangeRestrict a) :
        (φ i).GNS →L[ℂ] (φ i).GNS) = (φ i).gnsStarAlgHom a := by
  rw [factorRangeEquiv_rangeRestrict]
  rfl

/-- The norm of `ι φ hφ i a` in `ReducedFreeProduct φ hφ` equals its operator norm in the GNS
representation of `φ i`. -/
@[simp]
theorem norm_ι (i : I) (a : A i) : ‖ι φ hφ i a‖ = ‖(φ i).gnsStarAlgHom a‖ := by
  have hisom := StarAlgEquiv.isometry (factorRangeEquiv φ hφ i)
  have hnorm : ‖factorRangeEquiv φ hφ i ((ι φ hφ i).rangeRestrict a)‖ =
      ‖(ι φ hφ i).rangeRestrict a‖ :=
    hisom.norm_map_of_map_zero (map_zero _) _
  rw [factorRangeEquiv_rangeRestrict] at hnorm
  exact hnorm.symm

/-- `ι φ hφ i` is injective whenever the GNS representation of `φ i` is injective. -/
theorem ι_injective_of_gnsStarAlgHom_injective (i : I)
    (hi : Function.Injective (φ i).gnsStarAlgHom) :
    Function.Injective (ι φ hφ i) := by
  refine (injective_iff_map_eq_zero (ι φ hφ i)).mpr fun a ha => ?_
  exact (injective_iff_map_eq_zero (φ i).gnsStarAlgHom).mp hi a
    ((ι_eq_zero_iff_gnsStarAlgHom φ hφ i a).mp ha)

/-- `ι φ hφ i` is an isometry whenever the GNS representation of `φ i` is injective. -/
theorem isometry_ι_of_gnsStarAlgHom_injective (i : I)
    (hi : Function.Injective (φ i).gnsStarAlgHom) :
    Isometry (ι φ hφ i) :=
  NonUnitalStarAlgHom.isometry (ι φ hφ i)
    (ι_injective_of_gnsStarAlgHom_injective φ hφ i hi)

/-- `ι φ hφ i` is injective whenever the factor state `φ i` is faithful. -/
theorem ι_injective (i : I) (hi : ∀ a : A i, φ i (star a * a) = 0 → a = 0) :
    Function.Injective (ι φ hφ i) :=
  ι_injective_of_gnsStarAlgHom_injective φ hφ i
    ((φ i).gnsNonUnitalStarAlgHom_injective hi)

/-- `ι φ hφ i` is an isometry whenever the factor state `φ i` is faithful. -/
theorem isometry_ι (i : I) (hi : ∀ a : A i, φ i (star a * a) = 0 → a = 0) :
    Isometry (ι φ hφ i) :=
  NonUnitalStarAlgHom.isometry (ι φ hφ i) (ι_injective φ hφ i hi)

/-! ### Unitary identification with GNS of the reduced state -/

/-- Canonical unitary equivalence between the GNS Hilbert space of `state φ hφ` and
`Hilbert φ hφ`. -/
def gnsEquiv : (state φ hφ).GNS ≃ₗᵢ[ℂ] Hilbert φ hφ :=
  (state φ hφ).gnsEquiv (toOperator φ hφ).toNonUnitalStarAlgHom (vacuum φ hφ)
    (denseRange_toOperator_vacuum φ hφ) fun x => (state_apply φ hφ x).symm

@[simp]
theorem gnsEquiv_apply_gnsVector :
    gnsEquiv φ hφ (state φ hφ).gnsVector = vacuum φ hφ :=
  (state φ hφ).gnsEquiv_apply_gnsVector (toOperator φ hφ) (vacuum φ hφ)
    (denseRange_toOperator_vacuum φ hφ) fun x => (state_apply φ hφ x).symm

@[simp]
theorem gnsEquiv_symm_vacuum :
    (gnsEquiv φ hφ).symm (vacuum φ hφ) = (state φ hφ).gnsVector :=
  (state φ hφ).gnsEquiv_symm_apply_self (toOperator φ hφ) (vacuum φ hφ)
    (denseRange_toOperator_vacuum φ hφ) fun x => (state_apply φ hφ x).symm

@[simp↓]
theorem gnsEquiv_intertwines (x : ReducedFreeProduct φ hφ) (v : (state φ hφ).GNS) :
    gnsEquiv φ hφ ((state φ hφ).gnsStarAlgHom x v) = toOperator φ hφ x (gnsEquiv φ hφ v) :=
  (state φ hφ).gnsEquiv_intertwines_unital (toOperator φ hφ) (vacuum φ hφ)
    (denseRange_toOperator_vacuum φ hφ) (fun y => (state_apply φ hφ y).symm) x v

@[simp]
theorem gnsEquiv_symm_intertwines (x : ReducedFreeProduct φ hφ) (w : Hilbert φ hφ) :
    (gnsEquiv φ hφ).symm (toOperator φ hφ x w) =
      (state φ hφ).gnsStarAlgHom x ((gnsEquiv φ hφ).symm w) :=
  (state φ hφ).gnsEquiv_symm_intertwines_unital (toOperator φ hφ) (vacuum φ hφ)
    (denseRange_toOperator_vacuum φ hφ) (fun y => (state_apply φ hφ y).symm) x w

theorem gnsEquiv_apply_toGNS_of (y : LinearAlgebra.FreeProduct ℂ A) :
    gnsEquiv φ hφ ((state φ hφ).toGNS (of φ hφ y)) =
      (reducedFreeProductFunctional φ hφ).hilbertClassMap y := by
  have h1 := PositiveLinearMap.gnsEquiv_apply_coe (state φ hφ)
    (toOperator φ hφ).toNonUnitalStarAlgHom (vacuum φ hφ)
    (denseRange_toOperator_vacuum φ hφ) (fun x => (state_apply φ hφ x).symm) (of φ hφ y)
  have h2 := (reducedFreeProductFunctional φ hφ).boundedRepresentation_hilbertCyclicVector
    (freeProduct_continuous_leftMul _) y
  simp [gnsEquiv, PositiveLinearMap.toGNS_apply, toOperator_of, reducedFreeProductRep,
    vacuum_def] at h1 h2 ⊢

/-! ### Empty and singleton index identifications -/

/-- Over an empty index type, the reduced C⋆-free product is canonically `⋆`-isomorphic to `ℂ`.
-/
def isEmptyStarAlgEquiv [IsEmpty I] : ReducedFreeProduct φ hφ ≃⋆ₐ[ℂ] ℂ :=
  let f : ℂ →⋆ₐ[ℂ] ReducedFreeProduct φ hφ := StarAlgHom.ofId ℂ (ReducedFreeProduct φ hφ)
  have hdense : DenseRange f := by
    rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
    intro x
    have hs : Set.range (of φ hφ) ⊆ Set.range f := by
      rintro _ ⟨y, rfl⟩
      let r : ℂ := LinearAlgebra.FreeProduct.isEmptyStarAlgEquiv ℂ A y
      have hy : y = algebraMap ℂ (LinearAlgebra.FreeProduct ℂ A) r := by
        simpa only [r, LinearAlgebra.FreeProduct.isEmptyStarAlgEquiv_symm_apply] using
          ((LinearAlgebra.FreeProduct.isEmptyStarAlgEquiv ℂ A).symm_apply_apply y).symm
      refine ⟨r, ?_⟩
      rw [hy]
      exact (AlgHomClass.commutes (of φ hφ) r).symm
    exact closure_mono hs ((denseRange_of φ hφ).closure_range.symm ▸ Set.mem_univ x)
  (StarAlgEquiv.ofBijective f
    ⟨RingHom.injective f.toRingHom, f.surjective_of_denseRange hdense⟩).symm

@[simp]
theorem isEmptyStarAlgEquiv_symm_apply [IsEmpty I] (c : ℂ) :
    (isEmptyStarAlgEquiv φ hφ).symm c = algebraMap ℂ (ReducedFreeProduct φ hφ) c :=
  (rfl)

@[simp]
theorem isEmptyStarAlgEquiv_apply [IsEmpty I] (x : ReducedFreeProduct φ hφ) :
    isEmptyStarAlgEquiv φ hφ x = state φ hφ x := by
  have hx := (isEmptyStarAlgEquiv φ hφ).symm_apply_apply x
  rw [isEmptyStarAlgEquiv_symm_apply] at hx
  conv_rhs => rw [← hx]
  simp [Algebra.algebraMap_eq_smul_one]

/-- Over a singleton index type, the canonical factor map `ι φ hφ default` is surjective. -/
theorem unique_ι_surjective [Unique I] : Function.Surjective (ι φ hφ default) := by
  let π : LinearAlgebra.FreeProduct ℂ A →⋆ₐ[ℂ] A default :=
    LinearAlgebra.FreeProduct.liftStar fun {i} =>
      Eq.ndrec (motive := fun j => A i →⋆ₐ[ℂ] A j) (StarAlgHom.id ℂ (A i)) (Unique.eq_default i)
  have hcomp : (ιStar ℂ A default).comp π = StarAlgHom.id ℂ (LinearAlgebra.FreeProduct ℂ A) := by
    ext i a
    have heq : ∀ j (h : i = j),
        LinearAlgebra.FreeProduct.ι ℂ A j
            ((Eq.ndrec (motive := fun k => A i →⋆ₐ[ℂ] A k)
              (StarAlgHom.id ℂ (A i)) h) a) =
          LinearAlgebra.FreeProduct.ι ℂ A i a := by
      rintro _ rfl
      rfl
    simpa [π] using heq default (Unique.eq_default i)
  refine (ι φ hφ default).surjective_of_denseRange ?_
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro x
  have hs : Set.range (of φ hφ) ⊆ Set.range (ι φ hφ default) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨π y, ?_⟩
    calc
      ι φ hφ default (π y) = of φ hφ (ιStar ℂ A default (π y)) := rfl
      _ = of φ hφ y := congrArg (of φ hφ) (DFunLike.congr_fun hcomp y)
  exact closure_mono hs ((denseRange_of φ hφ).closure_range.symm ▸ Set.mem_univ x)

private def topRangeEquiv {B C : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    [Ring C] [StarRing C] [Algebra ℂ C] [StarModule ℂ C]
    (f : B →⋆ₐ[ℂ] C) (hf : Function.Surjective f) : C ≃⋆ₐ[ℂ] f.range where
  toFun c := ⟨c, hf c⟩
  invFun y := y.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Over a singleton index type, the reduced C⋆-free product is canonically `⋆`-isomorphic to
the range of the GNS representation of `φ default`. -/
def uniqueStarAlgEquiv [Unique I] :
    ReducedFreeProduct φ hφ ≃⋆ₐ[ℂ] (φ default).gnsStarAlgHom.range :=
  (topRangeEquiv (ι φ hφ default) (unique_ι_surjective φ hφ)).trans
    (factorRangeEquiv φ hφ default)

@[simp]
theorem uniqueStarAlgEquiv_ι [Unique I] (a : A default) :
    uniqueStarAlgEquiv φ hφ (ι φ hφ default a) = (φ default).gnsStarAlgHom.rangeRestrict a :=
  factorRangeEquiv_rangeRestrict φ hφ default a

/-- Over a singleton index type with a faithful state `φ default`, the reduced C⋆-free product
is canonically `⋆`-isomorphic to `A default`. -/
def uniqueStarAlgEquivOfFaithful [Unique I]
    (h : ∀ a : A default, φ default (star a * a) = 0 → a = 0) :
    ReducedFreeProduct φ hφ ≃⋆ₐ[ℂ] A default :=
  (StarAlgEquiv.ofBijective (ι φ hφ default)
    ⟨ι_injective φ hφ default h, unique_ι_surjective φ hφ⟩).symm

@[simp]
theorem uniqueStarAlgEquivOfFaithful_ι [Unique I]
    (h : ∀ a : A default, φ default (star a * a) = 0 → a = 0) (a : A default) :
    uniqueStarAlgEquivOfFaithful φ hφ h (ι φ hφ default a) = a :=
  (StarAlgEquiv.ofBijective (ι φ hφ default) _).symm_apply_apply a

@[simp]
theorem uniqueStarAlgEquivOfFaithful_symm_apply [Unique I]
    (h : ∀ a : A default, φ default (star a * a) = 0 → a = 0) (a : A default) :
    (uniqueStarAlgEquivOfFaithful φ hφ h).symm a = ι φ hφ default a :=
  (rfl)

end ReducedFreeProduct

end Construction

end TauCeti
