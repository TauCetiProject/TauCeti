/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Completion.Topology

import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Coefficient and root-order functoriality of the cyclotomic completion

Habiro's cyclotomic completion `CycloCompletion R S` is functorial in two directions:

1. **Order restriction** (`TauCeti.CycloCompletion.restrict`): for `T ⊆ S`,
   `cycloIndex R T ≤ cycloIndex R S`, giving a continuous `R`-algebra homomorphism
   `CycloCompletion R S →ₐ[R] CycloCompletion R T` that forgets quotient coordinates outside
   `cycloIndex R T`.
2. **Coefficient change** (`TauCeti.CycloCompletion.map`, `TauCeti.CycloCompletion.mapAlgHom`):
   for a ring homomorphism `φ : R →+* R'`, polynomial base change carries `cycloIndex R S` onto
   `cycloIndex R' S`, so `(fromPoly R' S).comp (Polynomial.mapRingHom φ)` is `S`-cyclotomically
   continuous and extends uniquely to a continuous ring homomorphism
   `CycloCompletion R S →+* CycloCompletion R' S` (an `A`-algebra homomorphism when `φ` is an
   `A`-algebra map).

Order restriction and coefficient change commute (`CycloCompletion.restrict_map`). At any finite
index `f : cycloIndex R S`, scalar extension along `R → R'` on the completed quotient modulo `f`
recovers the completed quotient of `CycloCompletion R' S` modulo `f.map (algebraMap R R')` via
ordinary tensor product (`CycloCompletion.tensorQuotientSpanAlgEquiv`).

Following Habiro (Lemma 3.1), `CycloCompletion.map φ S` preserves both injectivity and
surjectivity:

* when `φ` is injective, monic division remainders commute with `Polynomial.map φ`, giving
  injectivity at every finite quotient and hence on `CycloCompletion R S`
  (`CycloCompletion.map_injective`);
* when `φ` is surjective, inductively lifting successive residual quotients along the countable
  cofinal chain `cycloChain R S` constructs a preimage in `CycloCompletion R S`
  (`CycloCompletion.map_surjective`).

## Main definitions

* `TauCeti.CycloCompletion.restrict`: root-order restriction
  `CycloCompletion R S →ₐ[R] CycloCompletion R T` for `T ⊆ S`.
* `TauCeti.CycloCompletion.map`, `TauCeti.CycloCompletion.mapAlgHom`: coefficient functoriality
  along `φ : R →+* R'` (respectively `φ : R →ₐ[A] R'`).
* `TauCeti.CycloCompletion.tensorQuotientSpanAlgEquiv`: finite-level base-change isomorphism
  `R' ⊗[R] (CycloCompletion R S ⧸ (f)) ≃ₐ[R'] CycloCompletion R' S ⧸ (f.map (algebraMap R R'))`.

## Main results

* `TauCeti.CycloCompletion.continuous_restrict`, `TauCeti.CycloCompletion.continuous_map`:
  continuity of `restrict` and `map`.
* `TauCeti.CycloCompletion.restrict_map`: commuting square between `restrict` and `map`.
* `TauCeti.CycloCompletion.map_injective`: `map φ S` is injective when `φ` is injective.
* `TauCeti.CycloCompletion.map_surjective`: `map φ S` is surjective when `φ` is surjective.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §3.1 (Lemma 3.1) and §5 (proof of Theorem 5.2).
-/

public section

open Filter Polynomial TensorProduct
open scoped Topology

namespace TauCeti

namespace CycloCompletion

open PolyFamilyLimit

section Restrict

variable {R : Type*} [CommRing R]

/-- Root-order restriction `CycloCompletion R S →ₐ[R] CycloCompletion R T` for `T ⊆ S`, forgetting
quotient coordinates outside `cycloIndex R T`. -/
noncomputable def restrict (R : Type*) [CommRing R] {S T : Set ℕ} (hTS : T ⊆ S) :
    CycloCompletion R S →ₐ[R] CycloCompletion R T :=
  liftCompatAlgHom (g := fun f : cycloIndex R T ↦ (f : R[X]))
    (fun f ↦ proj (g := fun f : cycloIndex R S ↦ (f : R[X]))
      (Submonoid.inclusion (cycloIndex_mono hTS) f))
    (fun f f' h ↦ algHomOfDvd_comp_proj (g := fun f : cycloIndex R S ↦ (f : R[X]))
      (i := Submonoid.inclusion (cycloIndex_mono hTS) f)
      (j := Submonoid.inclusion (cycloIndex_mono hTS) f') h)

@[simp]
theorem proj_restrict {S T : Set ℕ} (hTS : T ⊆ S) (f : cycloIndex R T)
    (x : CycloCompletion R S) :
    proj f (restrict R hTS x) = proj (Submonoid.inclusion (cycloIndex_mono hTS) f) x :=
  proj_liftCompatAlgHom _ f x

@[simp]
theorem restrict_fromPoly {S T : Set ℕ} (hTS : T ⊆ S) (p : R[X]) :
    restrict R hTS (fromPoly R S p) = fromPoly R T p := by
  ext f
  rw [proj_restrict, proj_fromPoly, proj_fromPoly]
  rfl

@[simp]
theorem restrict_comp_fromPoly {S T : Set ℕ} (hTS : T ⊆ S) :
    (restrict R hTS).comp (fromPoly R S) = fromPoly R T :=
  AlgHom.ext (restrict_fromPoly hTS)

@[simp]
theorem restrict_rfl (R : Type*) [CommRing R] (S : Set ℕ) :
    restrict R (Set.Subset.rfl : S ⊆ S) = AlgHom.id R (CycloCompletion R S) := by
  refine AlgHom.ext fun x ↦ ext fun f ↦ ?_
  rw [proj_restrict, AlgHom.id_apply]
  rfl

theorem restrict_rfl_apply {S : Set ℕ} (x : CycloCompletion R S) :
    restrict R (Set.Subset.rfl : S ⊆ S) x = x := by
  rw [restrict_rfl, AlgHom.id_apply]

theorem restrict_comp {S T U : Set ℕ} (hUT : U ⊆ T) (hTS : T ⊆ S) :
    (restrict R hUT).comp (restrict R hTS) = restrict R (hUT.trans hTS) := by
  refine AlgHom.ext fun x ↦ ext fun f ↦ ?_
  rw [AlgHom.comp_apply, proj_restrict, proj_restrict, proj_restrict]
  rfl

@[simp]
theorem restrict_restrict {S T U : Set ℕ} (hUT : U ⊆ T) (hTS : T ⊆ S)
    (x : CycloCompletion R S) :
    restrict R hUT (restrict R hTS x) = restrict R (hUT.trans hTS) x :=
  AlgHom.congr_fun (restrict_comp hUT hTS) x

/-- Root-order restriction `restrict R hTS` is continuous. -/
@[fun_prop, continuity]
theorem continuous_restrict {S T : Set ℕ} (hTS : T ⊆ S) : Continuous (restrict R hTS) := by
  rw [continuous_iff]
  intro f
  have hcomp : (proj f ∘ restrict R hTS) =
      (proj (Submonoid.inclusion (cycloIndex_mono hTS) f) :
        CycloCompletion R S → AdjoinRoot (f : R[X])) :=
    funext (proj_restrict hTS f)
  rw [hcomp]
  exact isLocallyConstant_proj (Submonoid.inclusion (cycloIndex_mono hTS) f)

end Restrict

section Map

variable {R R' R'' : Type*} [CommRing R] [CommRing R'] [CommRing R'']

/-- Composing `Polynomial.mapRingHom φ` with `fromPoly R' S` yields an `S`-cyclotomically
continuous ring homomorphism `R[X] →+* CycloCompletion R' S`. -/
theorem isCycloContinuous_fromPoly_comp_mapRingHom (φ : R →+* R') (S : Set ℕ) :
    IsCycloContinuous S
      ((fromPoly R' S : R'[X] →+* CycloCompletion R' S).comp (Polynomial.mapRingHom φ)) :=
  (isCycloContinuous_fromPoly R' S).comp_mapRingHom φ

/-- The continuous ring homomorphism `CycloCompletion R S →+* CycloCompletion R' S` induced by a
ring homomorphism `φ : R →+* R'`. -/
noncomputable def map (φ : R →+* R') (S : Set ℕ) :
    CycloCompletion R S →+* CycloCompletion R' S :=
  lift S (isCycloContinuous_fromPoly_comp_mapRingHom φ S)

@[simp]
theorem map_fromPoly (φ : R →+* R') (S : Set ℕ) (p : R[X]) :
    map φ S (fromPoly R S p) = fromPoly R' S (p.map φ) :=
  lift_fromPoly (isCycloContinuous_fromPoly_comp_mapRingHom φ S) p

@[simp]
theorem map_comp_fromPoly (φ : R →+* R') (S : Set ℕ) :
    (map φ S).comp (fromPoly R S : R[X] →+* CycloCompletion R S) =
      (fromPoly R' S : R'[X] →+* CycloCompletion R' S).comp (Polynomial.mapRingHom φ) :=
  lift_comp_fromPoly (isCycloContinuous_fromPoly_comp_mapRingHom φ S)

theorem map_fromPoly_X (φ : R →+* R') (S : Set ℕ) :
    map φ S (fromPoly R S X) = fromPoly R' S X := by
  rw [map_fromPoly, Polynomial.map_X]

theorem map_fromPoly_C (φ : R →+* R') (S : Set ℕ) (r : R) :
    map φ S (fromPoly R S (C r)) = fromPoly R' S (C (φ r)) := by
  rw [map_fromPoly, Polynomial.map_C]

@[simp]
theorem map_algebraMap (φ : R →+* R') (S : Set ℕ) (r : R) :
    map φ S (algebraMap R (CycloCompletion R S) r) =
      algebraMap R' (CycloCompletion R' S) (φ r) := by
  rw [← fromPoly_C, map_fromPoly_C, fromPoly_C]

/-- The coefficient-change homomorphism `map φ S` is continuous. -/
@[fun_prop, continuity]
theorem continuous_map (φ : R →+* R') (S : Set ℕ) : Continuous (map φ S) :=
  continuous_lift (isCycloContinuous_fromPoly_comp_mapRingHom φ S)

/-- Compatibility of `CycloCompletion.map` with quotient projections: whenever `f' ∣ f.map φ`, the
`f'`-projection of `map φ S x` is the image of `proj f x` under `AdjoinRoot.map`. -/
theorem proj_map (φ : R →+* R') {S : Set ℕ} {f : cycloIndex R S} {f' : cycloIndex R' S}
    (h : (f' : R'[X]) ∣ (f : R[X]).map φ) (x : CycloCompletion R S) :
    proj f' (map φ S x) = AdjoinRoot.map φ (f : R[X]) (f' : R'[X]) h (proj f x) := by
  let _ : TopologicalSpace (AdjoinRoot (f' : R'[X])) := ⊥
  have : DiscreteTopology (AdjoinRoot (f' : R'[X])) := discreteTopology_bot _
  let lhs : CycloCompletion R S →+* AdjoinRoot (f' : R'[X]) :=
    ((proj f' : CycloCompletion R' S →ₐ[R'] _) : CycloCompletion R' S →+* _).comp (map φ S)
  let rhs : CycloCompletion R S →+* AdjoinRoot (f' : R'[X]) :=
    (AdjoinRoot.map φ (f : R[X]) (f' : R'[X]) h).comp
      ((proj f : CycloCompletion R S →ₐ[R] _) : CycloCompletion R S →+* _)
  have hlhs : Continuous lhs := (continuous_proj f').comp (continuous_map φ S)
  have hrhs : Continuous rhs :=
    ((isLocallyConstant_proj f).comp (AdjoinRoot.map φ (f : R[X]) (f' : R'[X]) h)).continuous
  have heq : lhs = rhs := by
    refine ringHom_ext_of_continuous hlhs hrhs (RingHom.ext fun p ↦ ?_)
    simp [lhs, rhs]
  exact RingHom.congr_fun heq x

@[simp]
theorem map_id (R : Type*) [CommRing R] (S : Set ℕ) :
    map (RingHom.id R) S = RingHom.id (CycloCompletion R S) := by
  refine ringHom_ext_of_continuous (continuous_map _ _) continuous_id (RingHom.ext fun p ↦ ?_)
  simp

theorem map_id_apply {S : Set ℕ} (x : CycloCompletion R S) :
    map (RingHom.id R) S x = x := by
  rw [map_id, RingHom.id_apply]

theorem map_comp (ψ : R' →+* R'') (φ : R →+* R') (S : Set ℕ) :
    (map ψ S).comp (map φ S) = map (ψ.comp φ) S := by
  refine ringHom_ext_of_continuous ((continuous_map ψ S).comp (continuous_map φ S))
    (continuous_map (ψ.comp φ) S) (RingHom.ext fun p ↦ ?_)
  simp [Polynomial.map_map]

@[simp]
theorem map_map (ψ : R' →+* R'') (φ : R →+* R') {S : Set ℕ} (x : CycloCompletion R S) :
    map ψ S (map φ S x) = map (ψ.comp φ) S x :=
  RingHom.congr_fun (map_comp ψ φ S) x

/-- Root-order restriction and coefficient functoriality commute as ring homomorphisms. -/
theorem restrict_comp_map (φ : R →+* R') {S T : Set ℕ} (hTS : T ⊆ S) :
    (restrict R' hTS : CycloCompletion R' S →+* CycloCompletion R' T).comp (map φ S) =
      (map φ T).comp (restrict R hTS : CycloCompletion R S →+* CycloCompletion R T) := by
  refine ringHom_ext_of_continuous ((continuous_restrict hTS).comp (continuous_map φ S))
    ((continuous_map φ T).comp (continuous_restrict hTS)) (RingHom.ext fun p ↦ ?_)
  simp

/-- Root-order restriction and coefficient functoriality commute on elements. -/
@[simp]
theorem restrict_map (φ : R →+* R') {S T : Set ℕ} (hTS : T ⊆ S) (x : CycloCompletion R S) :
    restrict R' hTS (map φ S x) = map φ T (restrict R hTS x) :=
  RingHom.congr_fun (restrict_comp_map φ hTS) x

/-- `A`-algebra homomorphism version of `CycloCompletion.map` for an `A`-algebra homomorphism
`φ : R →ₐ[A] R'` over a common base commutative semiring `A`. -/
noncomputable def mapAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') (S : Set ℕ) :
    CycloCompletion R S →ₐ[A] CycloCompletion R' S :=
  liftAlgHom S (ψ := ((fromPoly R' S).restrictScalars A).comp (Polynomial.mapAlgHom φ))
    (isCycloContinuous_fromPoly_comp_mapRingHom (φ : R →+* R') S)

@[simp]
theorem coe_mapAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') (S : Set ℕ) :
    ⇑(mapAlgHom φ S) = ⇑(map (φ : R →+* R') S) :=
  coe_liftAlgHom _

@[simp]
theorem toRingHom_mapAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') (S : Set ℕ) :
    (mapAlgHom φ S : CycloCompletion R S →+* CycloCompletion R' S) = map (φ : R →+* R') S :=
  toRingHom_liftAlgHom _

@[simp]
theorem mapAlgHom_comp_fromPoly {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') (S : Set ℕ) :
    (mapAlgHom φ S).comp ((fromPoly R S).restrictScalars A) =
      ((fromPoly R' S).restrictScalars A).comp (Polynomial.mapAlgHom φ) :=
  liftAlgHom_comp_restrictScalars_fromPoly _

@[simp]
theorem mapAlgHom_id (A R : Type*) [CommSemiring A] [CommRing R] [Algebra A R] (S : Set ℕ) :
    mapAlgHom (AlgHom.id A R) S = AlgHom.id A (CycloCompletion R S) := by
  ext x
  simp

theorem mapAlgHom_comp {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A R'] [Algebra A R'']
    (ψ : R' →ₐ[A] R'') (φ : R →ₐ[A] R') (S : Set ℕ) :
    (mapAlgHom ψ S).comp (mapAlgHom φ S) = mapAlgHom (ψ.comp φ) S :=
  AlgHom.ext fun x ↦ by
    simp only [AlgHom.comp_apply, coe_mapAlgHom, map_map]
    rfl

@[fun_prop, continuity]
theorem continuous_mapAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') (S : Set ℕ) :
    Continuous (mapAlgHom φ S) :=
  continuous_liftAlgHom _

/-- Commuting square between `restrict` and `mapAlgHom` in the category of `A`-algebras. -/
theorem restrict_comp_mapAlgHom {A : Type*} [CommSemiring A] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') {S T : Set ℕ} (hTS : T ⊆ S) :
    ((restrict R' hTS).restrictScalars A).comp (mapAlgHom φ S) =
      (mapAlgHom φ T).comp ((restrict R hTS).restrictScalars A) := by
  ext x
  simp

end Map

section FiniteQuotientBaseChange

variable {R : Type*} [CommRing R] {S : Set ℕ}

/-- At any finite index `f : cycloIndex R S`, base change of the completed quotient
`CycloCompletion R S ⧸ Ideal.span {fromPoly R S f}` along `R → R'` is canonically isomorphic as an
`R'`-algebra to `CycloCompletion R' S ⧸ Ideal.span {fromPoly R' S (f.map (algebraMap R R'))}`. -/
noncomputable def tensorQuotientSpanAlgEquiv (R' : Type*) [CommRing R'] [Algebra R R']
    (f : cycloIndex R S) :
    R' ⊗[R] (CycloCompletion R S ⧸ Ideal.span {fromPoly R S (f : R[X])}) ≃ₐ[R']
      CycloCompletion R' S ⧸
        Ideal.span {fromPoly R' S ((f : R[X]).map (algebraMap R R'))} :=
  let f' : cycloIndex R' S := ⟨(f : R[X]).map (algebraMap R R'),
    map_mem_cycloIndex (algebraMap R R') f.property⟩
  (Algebra.TensorProduct.congr AlgEquiv.refl (quotientSpanAlgEquiv f)).trans <|
    (AdjoinRoot.algebraTensorAlgEquiv R' (f : R[X])).trans (quotientSpanAlgEquiv f').symm

theorem tensorQuotientSpanAlgEquiv_one_tmul_mk (R' : Type*) [CommRing R'] [Algebra R R']
    (f : cycloIndex R S) (x : CycloCompletion R S) :
    tensorQuotientSpanAlgEquiv R' f (1 ⊗ₜ Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (map (algebraMap R R') S x) := by
  let f' : cycloIndex R' S := ⟨(f : R[X]).map (algebraMap R R'),
    map_mem_cycloIndex (algebraMap R R') f.property⟩
  apply (quotientSpanAlgEquiv f').injective
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj f x)
  have h1 : tensorQuotientSpanAlgEquiv R' f (1 ⊗ₜ Ideal.Quotient.mk _ x) =
      (quotientSpanAlgEquiv f').symm
        (AdjoinRoot.algebraTensorAlgEquiv R' (f : R[X]) (1 ⊗ₜ proj f x)) := by
    simp [tensorQuotientSpanAlgEquiv, f']
  rw [h1, AlgEquiv.apply_symm_apply, quotientSpanAlgEquiv_mk,
    proj_map (algebraMap R R') (f := f) (f' := f') dvd_rfl x, ← hp,
    AdjoinRoot.algebraTensorAlgEquiv_one_tmul_mk, AdjoinRoot.map_mk]

@[simp]
theorem tensorQuotientSpanAlgEquiv_tmul_mk (R' : Type*) [CommRing R'] [Algebra R R']
    (f : cycloIndex R S) (r' : R') (x : CycloCompletion R S) :
    tensorQuotientSpanAlgEquiv R' f (r' ⊗ₜ Ideal.Quotient.mk _ x) =
      r' • Ideal.Quotient.mk _ (map (algebraMap R R') S x) := by
  have htmul : (r' ⊗ₜ Ideal.Quotient.mk _ x :
      R' ⊗[R] (CycloCompletion R S ⧸ Ideal.span {fromPoly R S (f : R[X])})) =
      r' • (1 ⊗ₜ Ideal.Quotient.mk _ x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [htmul, ← AlgEquiv.toLinearMap_apply, LinearMap.map_smul, AlgEquiv.toLinearMap_apply,
    tensorQuotientSpanAlgEquiv_one_tmul_mk]

@[simp]
theorem tensorQuotientSpanAlgEquiv_symm_mk_map (R' : Type*) [CommRing R'] [Algebra R R']
    (f : cycloIndex R S) (x : CycloCompletion R S) :
    (tensorQuotientSpanAlgEquiv R' f).symm
        (Ideal.Quotient.mk _ (map (algebraMap R R') S x)) =
      1 ⊗ₜ Ideal.Quotient.mk _ x :=
  (tensorQuotientSpanAlgEquiv R' f).symm_apply_eq.mpr
    (tensorQuotientSpanAlgEquiv_one_tmul_mk R' f x).symm

@[simp]
theorem tensorQuotientSpanAlgEquiv_symm_mk_fromPoly_X (R' : Type*) [CommRing R'] [Algebra R R']
    (f : cycloIndex R S) :
    (tensorQuotientSpanAlgEquiv R' f).symm
        (Ideal.Quotient.mk _ (fromPoly R' S X)) =
      1 ⊗ₜ Ideal.Quotient.mk _ (fromPoly R S X) := by
  rw [← map_fromPoly_X (algebraMap R R') S, tensorQuotientSpanAlgEquiv_symm_mk_map]

end FiniteQuotientBaseChange

section InjectiveAndSurjective

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- **Coefficient injectivity (Habiro, Lemma 3.1).** If `φ : R →+* R'` is injective, then
`CycloCompletion.map φ S : CycloCompletion R S →+* CycloCompletion R' S` is injective. -/
theorem map_injective {φ : R →+* R'} (hφ : Function.Injective φ) (S : Set ℕ) :
    Function.Injective (map φ S) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  ext f
  rw [map_zero]
  let f' : cycloIndex R' S := ⟨(f : R[X]).map φ, map_mem_cycloIndex φ f.property⟩
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_surjective (proj f x)
  have hproj := proj_map φ (f := f) (f' := f') dvd_rfl x
  rw [hx, map_zero, ← hr, AdjoinRoot.map_mk] at hproj
  have hdvd : (f : R[X]) ∣ r :=
    (Polynomial.map_dvd_map φ hφ (cycloIndex.monic f)).mp
      (AdjoinRoot.mk_eq_zero.mp hproj.symm)
  rw [← hr, AdjoinRoot.mk_eq_zero.mpr hdvd]

/-- **Coefficient surjectivity (Habiro, Lemma 3.1).** If `φ : R →+* R'` is surjective, then
`CycloCompletion.map φ S : CycloCompletion R S →+* CycloCompletion R' S` is surjective. -/
theorem map_surjective {φ : R →+* R'} (hφ : Function.Surjective φ) (S : Set ℕ) :
    Function.Surjective (map φ S) := by
  intro y
  -- Lift the successive polynomial quotients `(approxPoly y (N + 1) - approxPoly y N) / cycloChain`
  -- along `φ` and assemble their partial sums into a `cycloChain`-compatible sequence in `R[X]`.
  choose q' hq' using fun N : ℕ ↦ dvd_approxPoly_sub_of_le (Nat.le_succ N) y
  choose q hq using fun N : ℕ ↦ Polynomial.map_surjective φ hφ (q' N)
  let p : ℕ → R[X] := Nat.rec 0 fun N pN ↦ pN + cycloChain R S N * q N
  have hp_map : ∀ N : ℕ, (p N).map φ = approxPoly y N := by
    intro N
    induction N with
    | zero => simp [p]
    | succ N ih =>
      calc
        (p (N + 1)).map φ = (p N).map φ + (cycloChain R S N).map φ * (q N).map φ := by
          simp [p]
        _ = approxPoly y N + cycloChain R' S N * q' N := by
          rw [ih, map_cycloChain, hq N]
        _ = approxPoly y (N + 1) := by rw [← hq' N, add_sub_cancel]
  have hp_step : ∀ N : ℕ, cycloChain R S N ∣ p (N + 1) - p N := fun N ↦
    ⟨q N, by dsimp only [p]; ring⟩
  obtain ⟨x, hx⟩ := exists_proj_cycloChainIndex_eq_mk hp_step
  refine ⟨x, ext_of_cycloChain fun N ↦ ?_⟩
  have hchain : ((cycloChainIndex R' S N : cycloIndex R' S) : R'[X]) ∣
      ((cycloChainIndex R S N : cycloIndex R S) : R[X]).map φ := by
    rw [coe_cycloChainIndex, coe_cycloChainIndex, map_cycloChain]
  rw [proj_map φ hchain x, hx N, AdjoinRoot.map_mk, hp_map N, mk_approxPoly]

end InjectiveAndSurjective

end CycloCompletion

end TauCeti
