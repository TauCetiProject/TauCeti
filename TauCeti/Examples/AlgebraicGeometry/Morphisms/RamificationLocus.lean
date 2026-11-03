/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Flat
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Examples of ramification, non-étale and branch loci

For a field `k`, these examples compute the loci of three morphisms of affine spaces, testing
`AlgebraicGeometry.Scheme.Hom.ramificationLocus`, `nonEtaleLocus` and `branchLocus`:

* the closed immersion of the origin `Spec k ⟶ 𝔸¹_k` is unramified but not flat, so its
  ramification locus is empty while its non-étale locus is the whole of `Spec k`: the two loci in
  the source differ in general;
* in characteristic `p > 0`, the relative Frobenius `𝔸¹_k ⟶ 𝔸¹_k`, `t ↦ tᵖ`, is finite and
  dominant between regular integral schemes but ramified everywhere, since `d(tᵖ) = 0`. So purity
  of the ramification locus in codimension one must exclude a ramification locus that is the
  whole source;
* if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`, `(x, y) ↦ (u, v) = (x², y)`, is finite and dominant
  between regular integral schemes. Its ramification locus is `V(x)`
  (`TauCeti.AlgebraicGeometry.ramificationLocus_square`), and so is its non-étale locus
  (`TauCeti.AlgebraicGeometry.nonEtaleLocus_square`), as it must be by
  `AlgebraicGeometry.Scheme.Hom.ramificationLocus_eq_nonEtaleLocus`. In particular the map is not
  étale at the origin, where it is ramified at the codimension-one point `(x)`: purity of the
  branch locus cannot drop its hypothesis at codimension-one points. The branch locus is `V(u)`
  (`TauCeti.AlgebraicGeometry.branchLocus_square`), with generic point `(u)`
  (`TauCeti.AlgebraicGeometry.isGenericPoint_branchLocus_square`), at which the local ring of
  `𝔸²_k` has dimension one: the branch locus is irreducible of codimension one, as purity of the
  branch locus predicts.

The ramification loci are computed as supports of the module of Kähler differentials, through
`RingHom.support_subset_ramificationLocus_specMap` and
`AlgHom.ramificationLocus_specMap_subset_zeroLocus`.

## References

* [Stacks Project, Definition 29.36.1](https://stacks.math.columbia.edu/tag/02G4) and
  [Definition 29.37.1](https://stacks.math.columbia.edu/tag/02GI).
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Théorème 3.1.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace TauCeti

section ClosedImmersion

open Polynomial

variable (k : Type u) [Field k]

/-- *test_ramificationLocus_ne_nonEtaleLocus*: the origin `Spec k ⟶ 𝔸¹_k` is a closed
immersion. -/
example : IsClosedImmersion (Spec.map (CommRingCat.ofHom (evalRingHom (0 : k)))) :=
  IsClosedImmersion.spec_of_surjective _ fun a ↦ ⟨C a, eval_C⟩

/-- *test_ramificationLocus_ne_nonEtaleLocus*: the origin `Spec k ⟶ 𝔸¹_k` is unramified, so its
ramification locus is empty. -/
example : (Spec.map (CommRingCat.ofHom (evalRingHom (0 : k)))).ramificationLocus = ∅ := by
  algebraize [evalRingHom (0 : k)]
  have : Algebra.FormallyUnramified k[X] k :=
    .of_surjective (Algebra.ofId k[X] k) fun a ↦ ⟨C a, eval_C⟩
  rw [Scheme.Hom.ramificationLocus_specMap, Algebra.unramifiedLocus_eq_univ_iff.mpr this]
  exact Set.compl_univ

/-- *test_ramificationLocus_ne_nonEtaleLocus*: the origin `Spec k ⟶ 𝔸¹_k` is not flat, as `x`
kills `k`, so it is étale at no point: its non-étale locus is the whole of `Spec k`. -/
example : (Spec.map (CommRingCat.ofHom (evalRingHom (0 : k)))).nonEtaleLocus = Set.univ := by
  algebraize [evalRingHom (0 : k)]
  have : Algebra.FiniteType k[X] k :=
    .of_surjective (Algebra.ofId k[X] k) fun a ↦ ⟨C a, eval_C⟩
  have : Algebra.FinitePresentation k[X] k := Algebra.FinitePresentation.of_finiteType.mp this
  rw [Scheme.Hom.nonEtaleLocus_specMap]
  refine Set.eq_univ_of_forall fun q hq ↦ ?_
  -- `Spec k` is a point, so étaleness at `q` is étaleness of `k` over `k[X]`.
  have : Algebra.Etale k[X] k := Algebra.etaleLocus_eq_univ_iff_etale.mp
    (Set.eq_univ_of_forall fun q' ↦ Subsingleton.elim q q' ▸ hq)
  have hX := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := k)
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := k)))
  have h : (X : k[X]) • (1 : k) = (X : k[X]) • (0 : k) := by
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  exact one_ne_zero (hX h)

end ClosedImmersion

section Frobenius

open Polynomial

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- *test_ramificationLocus_frobenius*: the relative Frobenius `𝔸¹_k ⟶ 𝔸¹_k`, `t ↦ tᵖ`, is finite,
since `t` is a root of the monic polynomial `Yᵖ - tᵖ` over `k[tᵖ]`. -/
example : IsFinite (Spec.map (CommRingCat.ofHom (expand k p).toRingHom)) := by
  rw [IsFinite.SpecMap_iff]
  refine RingHom.IsIntegral.to_finite (fun f ↦ ?_) (.of_comp_finiteType (f := C) ?_)
  · have hX : (expand k p).toRingHom.IsIntegralElem X :=
      ⟨Polynomial.X ^ p - Polynomial.C X, monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero,
        by simp⟩
    induction f using Polynomial.induction_on with
    | C a => simpa using (expand k p).toRingHom.isIntegralElem_map (x := C a)
    | add f g hf hg => exact hf.add _ hg
    | monomial n a h => simpa [pow_succ, mul_assoc] using h.mul _ hX
  · convert (RingHom.finiteType_algebraMap (A := k) (B := k[X])).mpr inferInstance
    exact RingHom.ext fun a ↦ expand_C p a

/-- *test_ramificationLocus_frobenius*: the relative Frobenius `𝔸¹_k ⟶ 𝔸¹_k`, `t ↦ tᵖ`, is
dominant, since `expand k p` is injective. -/
example : IsDominant (Spec.map (CommRingCat.ofHom (expand k p).toRingHom)) :=
  ⟨RingHom.denseRange_comap_of_injective _ (expand_injective (Fact.out : p.Prime).pos)⟩

/-- *test_ramificationLocus_frobenius*: the relative Frobenius `𝔸¹_k ⟶ 𝔸¹_k`, `t ↦ tᵖ`, is
ramified at every point, since `d/dt` vanishes on `k[tᵖ]`. -/
example : (Spec.map (CommRingCat.ofHom (expand k p).toRingHom)).ramificationLocus = Set.univ := by
  have h := RingHom.support_subset_ramificationLocus_specMap (expand k p).toRingHom
    (derivative' (R := k)) (fun r ↦ by simp [derivative_expand]) ?_
  · exact Set.eq_univ_of_univ_subset (Module.support_of_isTorsionFree.symm.subset.trans h)
  · rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨X, by simp⟩

/-- *test_ramificationLocus_frobenius*: `𝔸¹_k` is regular. -/
example : AlgebraicGeometry.IsRegular (Spec (CommRingCat.of k[X])) := inferInstance

/-- *test_ramificationLocus_frobenius*: `𝔸¹_k` is integral. -/
example : IsIntegral (Spec (CommRingCat.of k[X])) := inferInstance

end Frobenius

section Square

open MvPolynomial

variable (k : Type u) [Field k]

/-- The squaring map `(x, y) ↦ (u, v) = (x², y)` on coordinate rings, `u ↦ x²` and `v ↦ y`. -/
private noncomputable abbrev squareMap : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0 ^ 2, X 1]

private theorem squareMap_X_zero : squareMap k (X 0) = X 0 ^ 2 := by simp [squareMap]

private theorem squareMap_X_one : squareMap k (X 1) = X 1 := by simp [squareMap]

/-- Over `k[y]`, the squaring map is the expansion `x ↦ x²` of polynomials in `x`. -/
private theorem finSuccEquiv_squareMap (f : MvPolynomial (Fin 2) k) :
    finSuccEquiv k 1 (squareMap k f) = Polynomial.expand _ 2 (finSuccEquiv k 1 f) := by
  have h1 : finSuccEquiv k 1 (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
  have H : (finSuccEquiv k 1).toRingHom.comp (squareMap k).toRingHom =
      (Polynomial.expand _ 2).toRingHom.comp (finSuccEquiv k 1).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
    · simp [squareMap, finSuccEquiv_apply]
    · fin_cases i <;> simp [squareMap, h1, finSuccEquiv_X_zero]
  simpa using RingHom.congr_fun H f

private theorem squareMap_injective : Function.Injective (squareMap k) := fun f g h ↦
  (finSuccEquiv k 1).injective <| Polynomial.expand_injective two_pos <| by
    rw [← finSuccEquiv_squareMap, ← finSuccEquiv_squareMap, h]

/-- The ramification locus of the squaring map lies in `V(x)` when `2 ≠ 0` in `k`. -/
private theorem ramificationLocus_squareMap_subset (h2 : (2 : k) ≠ 0) :
    (Spec.map (CommRingCat.ofHom (squareMap k).toRingHom)).ramificationLocus ⊆
      PrimeSpectrum.zeroLocus {X 0} := by
  refine AlgHom.ramificationLocus_specMap_subset_zeroLocus _ _ fun M _ _ _ _ D hD t ↦ ?_
  -- A derivation vanishing on `x²` and `y` is killed by `x`, since `2` is a unit.
  have hu : IsUnit (2 : MvPolynomial (Fin 2) k) := by
    have := (IsUnit.mk0 _ h2).map (C : k →+* MvPolynomial (Fin 2) k)
    rwa [map_ofNat] at this
  have h0 : (X 0 : MvPolynomial (Fin 2) k) • D (X 0) = 0 := by
    have := hD (X 0)
    rw [squareMap_X_zero, pow_two, D.leibniz, ← two_smul (MvPolynomial (Fin 2) k)] at this
    exact (smul_eq_zero_iff_eq hu.unit).mp this
  have h1 : D (X 1) = 0 := by simpa [squareMap_X_one] using hD (X 1)
  -- So the derivation `x • D` vanishes on both variables.
  exact derivation_eq_zero_of_forall_mem_vars (D := (X 0 : MvPolynomial (Fin 2) k) • D) (f := t)
    fun i _ ↦ by fin_cases i <;> simp [h0, h1]

/-- The ramification locus of the squaring map contains `V(x)`. -/
private theorem zeroLocus_subset_ramificationLocus_squareMap :
    PrimeSpectrum.zeroLocus {X 0} ⊆
      (Spec.map (CommRingCat.ofHom (squareMap k).toRingHom)).ramificationLocus := by
  -- The derivation `∂/∂x` modulo `x` vanishes on `x²` and `y` and sends `x` to `1`.
  let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0}
  let D : Derivation k (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k ⧸ I) :=
    I.mkQ.compDer (pderiv 0)
  have hD : ∀ t, D t = Ideal.Quotient.mk I (pderiv 0 t) := fun _ ↦ by simp [D]
  refine subset_trans (le_of_eq ?_) (RingHom.support_subset_ramificationLocus_specMap
    (squareMap k).toRingHom D (fun r ↦ ?_) ?_)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_span]
  · -- `D` vanishes on the generators `x²` and `y` of the image of the squaring map.
    have hgen : Set.EqOn D (0 : Derivation k _ _) (Set.range ![X 0 ^ 2, X 1]) := by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · have hx : (2 * X 0 : MvPolynomial (Fin 2) k) ∈ I := I.mul_mem_left 2 (Ideal.subset_span rfl)
        simpa [hD] using Ideal.Quotient.eq_zero_iff_mem.mpr hx
      · simp [hD]
    have hr : squareMap k r ∈ Algebra.adjoin k (Set.range ![X 0 ^ 2, X 1]) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨r, rfl⟩
    simpa using D.eqOn_adjoin hgen hr
  · rw [eq_top_iff]
    rintro m -
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective m
    have : Ideal.Quotient.mk I t = t • D (X 0) := by
      simpa [hD] using Algebra.algebraMap_eq_smul_one (A := MvPolynomial (Fin 2) k ⧸ I) t
    rw [this]
    exact Submodule.smul_mem _ t (Submodule.subset_span ⟨X 0, rfl⟩)

/-- The squaring map sends `V(x)` onto `V(u)`. -/
private theorem image_comap_squareMap_zeroLocus :
    PrimeSpectrum.comap (squareMap k).toRingHom '' PrimeSpectrum.zeroLocus {X 0} =
      PrimeSpectrum.zeroLocus {X 0} := by
  refine subset_antisymm ?_ fun P hP ↦ ?_
  · rintro _ ⟨q, hq, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hq ⊢
    rw [SetLike.mem_coe, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    simpa [squareMap_X_zero] using Ideal.pow_mem_of_mem _ hq 2 two_pos
  · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hP
    -- `σ` sends `x` to `0` and fixes `y`, so `σ ∘ squareMap` is the identity modulo `u`.
    let σ : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k := (aeval ![0, X 1]).toRingHom
    have hσ : ((Ideal.Quotient.mk P.asIdeal).comp σ).comp (squareMap k).toRingHom =
        Ideal.Quotient.mk P.asIdeal := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
      · simp [σ, squareMap]
      · match i with
        | 0 => simpa [σ, squareMap] using (Ideal.Quotient.eq_zero_iff_mem.mpr hP).symm
        | 1 => simp [σ, squareMap]
    refine ⟨PrimeSpectrum.comap σ P, ?_, PrimeSpectrum.ext ?_⟩
    · simp [σ]
    · -- Both sides are kernels, of `σ ∘ squareMap` and of the identity modulo `P`.
      rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal,
        ← Ideal.mk_ker (I := P.asIdeal), RingHom.comap_ker, RingHom.comap_ker, hσ]

/-- *test_branchLocus_square*: if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`,
`(x, y) ↦ (x², y)`, has ramification locus `V(x)`. -/
theorem AlgebraicGeometry.ramificationLocus_square (h2 : (2 : k) ≠ 0) :
    (Spec.map (CommRingCat.ofHom
      (aeval ![X 0 ^ 2, X 1] : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
      ).ramificationLocus = PrimeSpectrum.zeroLocus {X 0} :=
  subset_antisymm (ramificationLocus_squareMap_subset k h2)
    (zeroLocus_subset_ramificationLocus_squareMap k)

/-- *test_branchLocus_square*: if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`,
`(x, y) ↦ (u, v) = (x², y)`, has branch locus `V(u)`. -/
theorem AlgebraicGeometry.branchLocus_square (h2 : (2 : k) ≠ 0) :
    (Spec.map (CommRingCat.ofHom
      (aeval ![X 0 ^ 2, X 1] : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
      ).branchLocus = PrimeSpectrum.zeroLocus {X 0} := by
  rw [Scheme.Hom.branchLocus_def, AlgebraicGeometry.ramificationLocus_square k h2]
  exact (Set.image_congr fun q _ ↦ Spec.map_apply _ q).trans (image_comap_squareMap_zeroLocus k)

/-- *test_purity_needs_codimOne*: `𝔸²_k`, the source and target of the squaring map, is
regular. -/
example : AlgebraicGeometry.IsRegular (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))) :=
  inferInstance

/-- *test_purity_needs_codimOne*: the map `𝔸²_k ⟶ 𝔸²_k`, `(x, y) ↦ (x², y)`, is finite, since
`x` is a root of the monic polynomial `T² - x²` over `k[x², y]`. -/
private theorem isFinite_specMap_squareMap :
    IsFinite (Spec.map (CommRingCat.ofHom (squareMap k).toRingHom)) := by
  rw [IsFinite.SpecMap_iff]
  refine RingHom.IsIntegral.to_finite (fun f ↦ ?_) (.of_comp_finiteType
    (f := algebraMap k (MvPolynomial (Fin 2) k)) ?_)
  · have hX (i : Fin 2) : (squareMap k).toRingHom.IsIntegralElem (X i) := by
      fin_cases i
      · exact ⟨Polynomial.X ^ 2 - Polynomial.C (X 0), Polynomial.monic_X_pow_sub_C _ two_ne_zero,
          by simp [squareMap]⟩
      · simpa [squareMap] using (squareMap k).toRingHom.isIntegralElem_map (x := X 1)
    induction f using MvPolynomial.induction_on with
    | C a => simpa using (squareMap k).toRingHom.isIntegralElem_map (x := C a)
    | add f g hf hg => exact hf.add _ hg
    | mul_X f i h => exact h.mul _ (hX i)
  · convert (RingHom.finiteType_algebraMap (A := k) (B := MvPolynomial (Fin 2) k)).mpr
      inferInstance
    exact RingHom.ext (squareMap k).commutes

/-- *test_purity_branchLocus_square*: the map `𝔸²_k ⟶ 𝔸²_k`, `(x, y) ↦ (x², y)`, is dominant,
since the substitution `(x, y) ↦ (x², y)` is injective. -/
private theorem isDominant_specMap_squareMap :
    IsDominant (Spec.map (CommRingCat.ofHom (squareMap k).toRingHom)) :=
  ⟨RingHom.denseRange_comap_of_injective _ (squareMap_injective k)⟩

/-- *test_purity_branchLocus_square*: if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`,
`(x, y) ↦ (x², y)`, has non-étale locus `V(x)`, equal to its ramification locus. -/
theorem AlgebraicGeometry.nonEtaleLocus_square (h2 : (2 : k) ≠ 0) :
    (Spec.map (CommRingCat.ofHom
      (aeval ![X 0 ^ 2, X 1] : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
      ).nonEtaleLocus = PrimeSpectrum.zeroLocus {X 0} := by
  have := isFinite_specMap_squareMap k
  have := isDominant_specMap_squareMap k
  rw [← Scheme.Hom.ramificationLocus_eq_nonEtaleLocus,
    AlgebraicGeometry.ramificationLocus_square k h2]

/-- *test_purity_needs_codimOne*: if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`, `(x, y) ↦ (x², y)`,
is not étale at the origin `(x, y)`, the kernel of the constant coefficient. The map is finite
and `𝔸²_k` is regular, but the map is ramified at the codimension-one point `(x)` specializing to
the origin. -/
example (h2 : (2 : k) ≠ 0) :
    (⟨RingHom.ker (constantCoeff : MvPolynomial (Fin 2) k →+* k),
      (RingHom.ker_isMaximal_of_surjective (constantCoeff : MvPolynomial (Fin 2) k →+* k)
        fun a ↦ ⟨C a, constantCoeff_C (Fin 2) a⟩).isPrime⟩ :
        Spec (CommRingCat.of (MvPolynomial (Fin 2) k))) ∈
    (Spec.map (CommRingCat.ofHom
      (aeval ![X 0 ^ 2, X 1] : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
      ).nonEtaleLocus := by
  rw [AlgebraicGeometry.nonEtaleLocus_square k h2]
  exact (PrimeSpectrum.mem_zeroLocus _ _).mpr <| Set.singleton_subset_iff.mpr <|
    RingHom.mem_ker.mpr (constantCoeff_X _ _)

/-- *test_purity_branchLocus_square*: if `2 ≠ 0` in `k`, the branch locus `V(u)` of the map
`𝔸²_k ⟶ 𝔸²_k`, `(x, y) ↦ (u, v) = (x², y)`, is irreducible, with generic point `(u)`. -/
theorem AlgebraicGeometry.isGenericPoint_branchLocus_square (h2 : (2 : k) ≠ 0) :
    IsGenericPoint (⟨Ideal.span {X 0}, (Ideal.span_singleton_prime (X_ne_zero _)).mpr prime_X⟩ :
        Spec (CommRingCat.of (MvPolynomial (Fin 2) k)))
      (Spec.map (CommRingCat.ofHom
        (aeval ![X 0 ^ 2, X 1] : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
        ).branchLocus := by
  rw [AlgebraicGeometry.branchLocus_square k h2, IsGenericPoint, PrimeSpectrum.closure_singleton,
    PrimeSpectrum.zeroLocus_span]

/-- *test_purity_branchLocus_square*: the point `(u)` of `𝔸²_k` has codimension one: the local
ring of `𝔸²_k` there has dimension one. If `2 ≠ 0` in `k`, then `(u)` is the generic point of the
branch locus of the map `𝔸²_k ⟶ 𝔸²_k`, `(x, y) ↦ (u, v) = (x², y)`
(`isGenericPoint_branchLocus_square`). -/
example :
    ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).presheaf.stalk
      (⟨Ideal.span {X 0}, (Ideal.span_singleton_prime (X_ne_zero _)).mpr prime_X⟩ :
        Spec (CommRingCat.of (MvPolynomial (Fin 2) k)))) = 1 := by
  -- `rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight]` cannot match: the point is
  -- elaborated as a `PrimeSpectrum` term rather than a point of `Spec`, so we chain with `trans`.
  refine (ringKrullDim_stalk_eq_coheight _).trans
    ((congrArg _ (idealHeight_eq_coheight _ _).symm).trans ?_)
  rw [Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)) prime_X.not_isUnit]
  norm_cast

end Square

end TauCeti
