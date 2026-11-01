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

/-!
# Examples of ramification, non-étale and branch loci

For a field `k`, these examples compute the loci of three morphisms of affine spaces, testing
`AlgebraicGeometry.Scheme.Hom.ramificationLocus`, `nonEtaleLocus` and `branchLocus`:

* the closed immersion of the origin `Spec k ⟶ 𝔸¹_k` is unramified but not flat, so its
  ramification locus is empty while its non-étale locus is the whole of `Spec k`: the two loci in
  the source differ in general;
* in characteristic `p`, the relative Frobenius `𝔸¹_k ⟶ 𝔸¹_k`, `t ↦ tᵖ`, is ramified everywhere,
  since `d(tᵖ) = 0`. Although it is a finite dominant morphism of regular integral schemes, its
  ramification locus is the whole source, so purity of the ramification locus in codimension one
  must exclude this case;
* if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`, `(x, y) ↦ (u, v) = (x², y)`, has ramification locus
  `V(x)` and branch locus `V(u)` (`TauCeti.AlgebraicGeometry.ramificationLocus_square` and
  `TauCeti.AlgebraicGeometry.branchLocus_square`).

The ramification loci are computed as supports of the module of Kähler differentials. A derivation
`S → M` over the base whose image spans `M` shows that the support of `M` lies in the ramification
locus, and an element of `S` annihilating every such derivation cuts the ramification locus down
to its zero locus. Both reductions are stated for a ring homomorphism rather than an algebra, since
in these examples the source and target rings are equal and an algebra structure would clash with
`Algebra.id`.

## References

* [Stacks Project, Definition 29.36.1](https://stacks.math.columbia.edu/tag/02G4) and
  [Definition 29.37.1](https://stacks.math.columbia.edu/tag/02GI).
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Théorème 3.1.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace TauCeti

section Derivation

variable {R S : Type u} [CommRing R] [CommRing S]

/-- If a derivation `S → M`, over any base, vanishes on the image of `φ : R →+* S` and its image
spans `M`, then the support of `M` lies in the ramification locus of `Spec S ⟶ Spec R`. -/
private theorem support_subset_ramificationLocus (φ : R →+* S) {A : Type*} [CommRing A]
    [Algebra A S] {M : Type u} [AddCommGroup M] [Module A M] [Module S M]
    (D : Derivation A S M) (hφ : ∀ r, D (φ r) = 0) (hD : Submodule.span S (Set.range D) = ⊤) :
    Module.support S M ⊆ (Spec.map (CommRingCat.ofHom φ)).ramificationLocus := by
  algebraize [φ]
  let : Module R M := Module.compHom M (algebraMap R S)
  have : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  -- Vanishing on the image of `φ` makes `D` linear over `R`.
  let D' : Derivation R S M := Derivation.mk'
    { toFun := D, map_add' := D.map_add, map_smul' := fun r s ↦ by
        rw [Algebra.smul_def, D.leibniz, RingHom.id_apply,
          ← IsScalarTower.algebraMap_smul S r (D s), RingHom.algebraMap_toAlgebra, hφ, smul_zero,
          add_zero] } fun a b ↦ D.leibniz a b
  have hsurj : Function.Surjective D'.liftKaehlerDifferential := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hD, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    exact ⟨KaehlerDifferential.D R S s, D'.liftKaehlerDifferential_comp_D s⟩
  refine (Module.support_subset_of_surjective _ hsurj).trans ?_
  rw [Scheme.Hom.ramificationLocus_specMap, Algebra.unramifiedLocus_eq_compl_support, compl_compl]

/-- If `s : S` annihilates every additive derivation `S → M` vanishing on the image of
`φ : R →+* S`, then the ramification locus of `Spec S ⟶ Spec R` lies in the zero locus of `s`. -/
private theorem ramificationLocus_subset_zeroLocus (φ : R →+* S) (s : S)
    (hs : ∀ (M : Type u) [AddCommGroup M] [Module S M] (D : Derivation ℤ S M),
      (∀ r, D (φ r) = 0) → ∀ t, s • D t = 0) :
    (Spec.map (CommRingCat.ofHom φ)).ramificationLocus ⊆ PrimeSpectrum.zeroLocus {s} := by
  algebraize [φ]
  rw [Scheme.Hom.ramificationLocus_specMap, Algebra.unramifiedLocus_eq_compl_support,
    compl_compl]
  intro p hp
  -- Apply the hypothesis to the universal derivation: `s` annihilates `Ω[S⁄R]`.
  have hann : s ∈ Module.annihilator S Ω[S⁄R] := by
    rw [Module.mem_annihilator]
    intro ω
    have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨t, rfl⟩ := h
      exact hs _ ((KaehlerDifferential.D R S).restrictScalars ℤ)
        (KaehlerDifferential.D R S).map_algebraMap t
    | zero => exact smul_zero s
    | add _ _ _ _ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]
    | smul a _ _ h => rw [smul_comm, h, smul_zero]
  exact Set.singleton_subset_iff.mpr (Module.annihilator_le_of_mem_support hp hann)

end Derivation

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
  have : Subsingleton Ω[k⁄k[X]] :=
    KaehlerDifferential.subsingleton_of_surjective _ _ fun a ↦ ⟨C a, eval_C⟩
  have : Algebra.FormallyUnramified k[X] k := ⟨inferInstance⟩
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
    rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra, coe_evalRingHom, eval_X,
      zero_mul]
  exact one_ne_zero (hX h)

end ClosedImmersion

section Frobenius

open Polynomial

variable (k : Type u) [Field k] (p : ℕ) [CharP k p]

/-- *test_ramificationLocus_frobenius*: in characteristic `p`, the map `𝔸¹_k ⟶ 𝔸¹_k`,
`t ↦ tᵖ`, is ramified at every point, since `d/dt` vanishes on `k[tᵖ]`. For `p > 0` this is the
relative Frobenius of `𝔸¹_k`. -/
example : (Spec.map (CommRingCat.ofHom (expand k p).toRingHom)).ramificationLocus = Set.univ := by
  have h := support_subset_ramificationLocus (expand k p).toRingHom (derivative' (R := k))
    (fun r ↦ ?_) ?_
  · have hu : Module.support k[X] k[X] = Set.univ := Set.eq_univ_of_forall fun q ↦ by
      rw [Module.mem_support_iff_of_finite, Module.annihilator_eq_bot.mpr inferInstance]
      exact bot_le
    exact Set.eq_univ_of_univ_subset (hu.symm.subset.trans h)
  · simp [derivative_expand]
  · rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨X, by simp⟩

end Frobenius

section Square

open MvPolynomial

variable (k : Type u) [Field k]

/-- The squaring map `(x, y) ↦ (u, v) = (x², y)` on coordinate rings, `u ↦ x²` and `v ↦ y`. -/
private noncomputable abbrev squareMap : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k :=
  (aeval ![X 0 ^ 2, X 1]).toRingHom

private theorem squareMap_X_zero : squareMap k (X 0) = X 0 ^ 2 := by simp [squareMap]

private theorem squareMap_X_one : squareMap k (X 1) = X 1 := by simp [squareMap]

private theorem squareMap_C (a : k) : squareMap k (C a) = C a := by simp [squareMap]

/-- The ramification locus of the squaring map is `V(x)` when `2 ≠ 0` in `k`. -/
private theorem ramificationLocus_squareMap (h2 : (2 : k) ≠ 0) :
    (Spec.map (CommRingCat.ofHom (squareMap k))).ramificationLocus =
      PrimeSpectrum.zeroLocus {X 0} := by
  refine subset_antisymm (ramificationLocus_subset_zeroLocus _ _ ?_) ?_
  · -- A derivation vanishing on `x²` and `y` is killed by `x`, since `2` is a unit.
    intro M _ _ D hD t
    have hu : IsUnit (2 : MvPolynomial (Fin 2) k) := by
      have := (IsUnit.mk0 _ h2).map (C : k →+* MvPolynomial (Fin 2) k)
      rwa [map_ofNat] at this
    have hX : ∀ i, (X 0 : MvPolynomial (Fin 2) k) • D (X i) = 0
      | 0 => by
        have := hD (X 0)
        rw [squareMap_X_zero, pow_two, D.leibniz, ← two_smul (MvPolynomial (Fin 2) k)] at this
        exact (smul_eq_zero_iff_eq hu.unit).mp this
      | 1 => by
        have := hD (X 1)
        rw [squareMap_X_one] at this
        rw [this, smul_zero]
    induction t using MvPolynomial.induction_on with
    | C a =>
      have := hD (C a)
      rw [squareMap_C] at this
      rw [this, smul_zero]
    | add p q hp hq => rw [map_add, smul_add, hp, hq, add_zero]
    | mul_X p i hp =>
      rw [D.leibniz, smul_add, smul_comm, hX, smul_zero, smul_comm, hp, smul_zero, add_zero]
  · -- The derivation `∂/∂x` modulo `x` vanishes on `x²` and `y` and sends `x` to `1`.
    let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {X 0}
    let D : Derivation k (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k ⧸ I) :=
      I.mkQ.compDer (pderiv 0)
    have hD : ∀ t, D t = Ideal.Quotient.mk I (pderiv 0 t) := fun _ ↦ rfl
    have h := support_subset_ramificationLocus (squareMap k) D (fun r ↦ ?_) ?_
    · refine subset_trans (le_of_eq ?_) h
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_span]
    · induction r using MvPolynomial.induction_on with
      | C a => rw [squareMap_C, hD, pderiv_C, map_zero]
      | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
      | mul_X p i hp =>
        rw [map_mul, D.leibniz, hp, smul_zero, add_zero]
        match i with
        | 0 =>
          have hx : X 0 ∈ I := Ideal.subset_span rfl
          rw [squareMap_X_zero, hD, Ideal.Quotient.eq_zero_iff_mem.mpr, smul_zero]
          rw [pow_two, Derivation.leibniz, pderiv_X_self, smul_eq_mul, mul_one]
          exact I.add_mem hx hx
        | 1 => rw [squareMap_X_one, hD, pderiv_X_of_ne (by decide), map_zero, smul_zero]
    · rw [eq_top_iff]
      rintro m -
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective m
      have h1 : D (X 0) = 1 := by rw [hD, pderiv_X_self, map_one]
      have : Ideal.Quotient.mk I t = t • D (X 0) := by
        rw [h1, ← map_one (Ideal.Quotient.mk I), ← Ideal.Quotient.mk_eq_mk,
          ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨X 0, rfl⟩)

/-- The squaring map sends `V(x)` onto `V(u)`. -/
private theorem image_comap_squareMap_zeroLocus :
    PrimeSpectrum.comap (squareMap k) '' PrimeSpectrum.zeroLocus {X 0} =
      PrimeSpectrum.zeroLocus {X 0} := by
  refine subset_antisymm ?_ fun P hP ↦ ?_
  · rintro _ ⟨q, hq, rfl⟩
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hq ⊢
    rw [SetLike.mem_coe, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, squareMap_X_zero]
    exact Ideal.pow_mem_of_mem _ hq 2 two_pos
  · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hP
    -- `σ` sends `x` to `0` and fixes `y`, so `σ ∘ squareMap` is the identity modulo `u`.
    let σ : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k := (aeval ![0, X 1]).toRingHom
    have hσ : ((Ideal.Quotient.mk P.asIdeal).comp σ).comp (squareMap k) =
        Ideal.Quotient.mk P.asIdeal := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
      · simp [σ, squareMap]
      · match i with
        | 0 => simpa [σ, squareMap] using (Ideal.Quotient.eq_zero_iff_mem.mpr hP).symm
        | 1 => simp [σ, squareMap]
    refine ⟨PrimeSpectrum.comap σ P, ?_, PrimeSpectrum.ext (Ideal.ext fun r ↦ ?_)⟩
    · simp [σ]
    · rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal,
        Ideal.mem_comap, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem,
        ← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, ← RingHom.comp_apply, hσ]

/-- *test_branchLocus_square*: if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`,
`(x, y) ↦ (x², y)`, has ramification locus `V(x)`. -/
theorem AlgebraicGeometry.ramificationLocus_square (h2 : (2 : k) ≠ 0) :
    (Spec.map (CommRingCat.ofHom
      (aeval ![X 0 ^ 2, X 1] : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
      ).ramificationLocus = PrimeSpectrum.zeroLocus {X 0} :=
  ramificationLocus_squareMap k h2

/-- *test_branchLocus_square*: if `2 ≠ 0` in `k`, the map `𝔸²_k ⟶ 𝔸²_k`,
`(x, y) ↦ (u, v) = (x², y)`, has branch locus `V(u)`. -/
theorem AlgebraicGeometry.branchLocus_square (h2 : (2 : k) ≠ 0) :
    (Spec.map (CommRingCat.ofHom
      (aeval ![X 0 ^ 2, X 1] : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k).toRingHom)
      ).branchLocus = PrimeSpectrum.zeroLocus {X 0} := by
  rw [Scheme.Hom.branchLocus_def, ramificationLocus_squareMap k h2]
  exact (Set.image_congr fun q _ ↦ Spec.map_apply _ q).trans (image_comap_squareMap_zeroLocus k)

end Square

end TauCeti
