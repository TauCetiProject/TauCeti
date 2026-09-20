/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The factor-field construction of the semi-local decomposition

For a finite extension of number fields `L/K`, choose a primitive element `α` and factor its
minimal polynomial over the completion `K_v`. The irreducible factors are in bijection with the
places `w` of `L` above `v`; their quotient fields are the completions `L_w`. The Chinese
remainder assembly of these factor fields agrees with `semilocalEquiv`.

This is the factor/CRT realization of Neukirch II, Proposition (8.3). The underlying semi-local
equivalence is constructed in `TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic` without
choosing a primitive element.

## Main definitions

* `TauCeti.semilocalPowerBasis`: the chosen primitive power basis of `L/K`.
* `TauCeti.completionPolynomial`: its minimal polynomial, extended to `K_v`.
* `TauCeti.completionFactors`: the normalized irreducible factors of that polynomial.
* `TauCeti.completionFactorsEquivPlaces`: the factors correspond to the places above `v`.
* `TauCeti.factorFieldEquivCompletion`: each factor field is the corresponding completion.
* `TauCeti.semilocalCrtEquiv`: the Chinese remainder assembly through the factor fields.

## Main results

* `TauCeti.completionPolynomial_eq_prod`: the completed minimal polynomial is the product of the
  factors attached to the places above `v`.
* `TauCeti.factorFieldEquivCompletion_algebraMap`: the factor-field equivalence is compatible
  with the canonical map from `L`.
* `TauCeti.semilocalEquiv_eq_crt`: the factor/CRT assembly is `semilocalEquiv`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, Proposition (8.3).
-/

public section
noncomputable section

open IsDedekindDomain NumberField Module Polynomial
open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/-- A chosen primitive power basis for a finite extension of number fields. -/
def semilocalPowerBasis : PowerBasis K L :=
  Field.powerBasisOfFiniteOfSeparable K L

/-- The minimal polynomial of the chosen primitive element of `L/K`, extended to `K_v`. -/
def completionPolynomial : (v.adicCompletion K)[X] :=
  (minpoly K (semilocalPowerBasis (K := K) L).gen).map
    (algebraMap K (v.adicCompletion K))

/-- The normalized irreducible factors over `K_v` of the chosen primitive element's minimal
polynomial. -/
abbrev completionFactors :=
  {q : (v.adicCompletion K)[X] //
    Irreducible q ∧ q.Monic ∧ q ∣ completionPolynomial L v}

private def semilocalTensorPowerBasis :
    PowerBasis (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) where
  gen := 1 ⊗ₜ (semilocalPowerBasis (K := K) L).gen
  dim := (semilocalPowerBasis (K := K) L).dim
  basis := (semilocalPowerBasis (K := K) L).basis.baseChange (v.adicCompletion K)
  basis_eq_pow i := by
    rw [Basis.baseChange_apply, (semilocalPowerBasis (K := K) L).basis_eq_pow]
    induction i.1 with
    | zero => simp only [pow_zero, Algebra.TensorProduct.one_def]
    | succ n ih =>
        rw [pow_succ, pow_succ, ← ih, Algebra.TensorProduct.tmul_mul_tmul]
        simp

private def semilocalPiPowerBasis :
    PowerBasis (v.adicCompletion K)
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
  (semilocalTensorPowerBasis L v).map (semilocalEquiv L v)

/-- The irreducible factor over `K_v` associated with a place `w` above `v`: the minimal
polynomial of the chosen primitive element in `L_w`. -/
abbrev completionFactor
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    (v.adicCompletion K)[X] :=
  minpoly (v.adicCompletion K)
    (algebraMap L (w.1.adicCompletion L) (semilocalPowerBasis (K := K) L).gen)

private theorem semilocalPiPowerBasis_gen
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    (semilocalPiPowerBasis L v).gen w =
      algebraMap L (w.1.adicCompletion L) (semilocalPowerBasis (K := K) L).gen := by
  simp [semilocalPiPowerBasis, semilocalTensorPowerBasis]

private theorem completionFactor_primitive
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    IntermediateField.adjoin (v.adicCompletion K) {(semilocalPiPowerBasis L v).gen w} = ⊤ := by
  have hsurj : Function.Surjective
      (aeval ((semilocalPiPowerBasis L v).gen w) :
        (v.adicCompletion K)[X] →ₐ[v.adicCompletion K] w.1.adicCompletion L) := by
    classical
    intro y
    let z : (u : {u : HeightOneSpectrum (𝒪 L) // u.asIdeal.LiesOver v.asIdeal}) →
        u.1.adicCompletion L := Pi.single w y
    obtain ⟨f, hf⟩ := (semilocalPiPowerBasis L v).exists_eq_aeval' z
    refine ⟨f, ?_⟩
    rw [← Polynomial.aeval_pi_apply₂ (R := v.adicCompletion K)
      (semilocalPiPowerBasis L v).gen f w]
    simpa [z, Pi.single_apply] using congrFun hf.symm w
  apply IntermediateField.toSubalgebra_injective
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (IsIntegral.of_finite (v.adicCompletion K) _).isAlgebraic]
  exact (Algebra.adjoin_singleton_eq_range_aeval _ _).trans
    ((AlgHom.range_eq_top _).2 hsurj)

private theorem completionFactor_monic
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    (completionFactor L v w).Monic :=
  minpoly.monic (IsIntegral.of_finite (v.adicCompletion K) _)

private theorem completionFactor_irreducible
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    Irreducible (completionFactor L v w) :=
  minpoly.irreducible (IsIntegral.of_finite (v.adicCompletion K) _)

private theorem completionFactor_dvd
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    completionFactor L v w ∣ completionPolynomial L v := by
  unfold completionFactor
  apply minpoly.dvd
  rw [completionPolynomial, aeval_map_algebraMap]
  simp

private theorem completionFactor_natDegree
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    (completionFactor L v w).natDegree =
      finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  rw [completionFactor, ← semilocalPiPowerBasis_gen L v w]
  exact (Field.primitive_element_iff_minpoly_natDegree_eq
    (v.adicCompletion K) ((semilocalPiPowerBasis L v).gen w)).mp
      (completionFactor_primitive L v w)

private theorem completionFactor_injective :
    Function.Injective (completionFactor L v) := by
  classical
  intro w u hfactor
  by_contra hwu
  let z : (t : {t : HeightOneSpectrum (𝒪 L) // t.asIdeal.LiesOver v.asIdeal}) →
      t.1.adicCompletion L := Pi.single u 1
  obtain ⟨f, hf⟩ := (semilocalPiPowerBasis L v).exists_eq_aeval' z
  have hfw : aeval ((semilocalPiPowerBasis L v).gen w) f = 0 := by
    rw [← Polynomial.aeval_pi_apply₂ (R := v.adicCompletion K)
      (semilocalPiPowerBasis L v).gen f w]
    simpa [z, Pi.single_apply, hwu] using congrFun hf.symm w
  rw [semilocalPiPowerBasis_gen L v w] at hfw
  have hdvdw : completionFactor L v w ∣ f := by
    unfold completionFactor
    exact minpoly.dvd (v.adicCompletion K) _ hfw
  have hdvdu : completionFactor L v u ∣ f := by
    rw [← hfactor]
    exact hdvdw
  have hfu : aeval
      (algebraMap L (u.1.adicCompletion L) (semilocalPowerBasis (K := K) L).gen) f = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero hdvdu
      (minpoly.aeval (v.adicCompletion K)
        (algebraMap L (u.1.adicCompletion L) (semilocalPowerBasis (K := K) L).gen))
  rw [← semilocalPiPowerBasis_gen L v u] at hfu
  have : (1 : u.1.adicCompletion L) = 0 := by
    rw [← hfu, ← Polynomial.aeval_pi_apply₂ (R := v.adicCompletion K)
      (semilocalPiPowerBasis L v).gen f u]
    simpa [z, Pi.single_apply] using congrFun hf u
  exact one_ne_zero this

private theorem completionFactor_pairwise_coprime :
    Pairwise fun w u ↦ IsCoprime (completionFactor L v w) (completionFactor L v u) := by
  intro w u hwu
  rw [(completionFactor_irreducible L v w).coprime_iff_not_dvd]
  intro hdvd
  have hassoc := (completionFactor_irreducible L v w).associated_of_dvd
    (completionFactor_irreducible L v u) hdvd
  exact hwu (completionFactor_injective L v
    (Polynomial.eq_of_monic_of_associated
      (completionFactor_monic L v w) (completionFactor_monic L v u) hassoc))

private theorem completionPolynomial_monic : (completionPolynomial L v).Monic := by
  exact (minpoly.monic (Algebra.IsIntegral.isIntegral
    (semilocalPowerBasis (K := K) L).gen)).map _

attribute [local instance] Fintype.ofFinite in
/-- **The factorization of the completed primitive polynomial.** Over `K_v`, the minimal
polynomial of the chosen primitive element of `L/K` is the product of the completion factors of
the places of `L` above `v`. -/
theorem completionPolynomial_eq_prod :
    completionPolynomial L v =
      ∏ w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal},
        completionFactor L v w := by
  classical
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_of_monic Finset.univ _ fun w _ ↦ completionFactor_monic L v w)
    (completionPolynomial_monic L v)
    (Fintype.prod_dvd_of_coprime (completionFactor_pairwise_coprime L v)
      (completionFactor_dvd L v))
  rw [Polynomial.natDegree_prod_of_monic _ _
    (fun w _ ↦ completionFactor_monic L v w)]
  simp_rw [completionFactor_natDegree]
  rw [sum_finrank_adicCompletion_eq_finrank]
  rw [completionPolynomial, natDegree_map]
  exact ((semilocalPowerBasis (K := K) L).natDegree_minpoly.trans
    (semilocalPowerBasis (K := K) L).finrank.symm).le

private def completionFactorOfPlace
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    completionFactors L v := by
  exact ⟨completionFactor L v w, completionFactor_irreducible L v w,
    completionFactor_monic L v w, completionFactor_dvd L v w⟩

private theorem completionFactorOfPlace_bijective :
    Function.Bijective (completionFactorOfPlace L v) := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  constructor
  · intro w u h
    exact completionFactor_injective L v (congr_arg Subtype.val h)
  · intro q
    have hq := q.2
    have hdvd : q.1 ∣ ∏ w : {w : HeightOneSpectrum (𝒪 L) //
        w.asIdeal.LiesOver v.asIdeal}, completionFactor L v w := by
      rw [← completionPolynomial_eq_prod L v]
      exact hq.2.2
    obtain ⟨w, _, hqw⟩ := (Prime.dvd_finsetProd_iff hq.1.prime (completionFactor L v)).1 hdvd
    have hassoc := hq.1.associated_of_dvd (completionFactor_irreducible L v w) hqw
    have heq := Polynomial.eq_of_monic_of_associated hq.2.1
      (completionFactor_monic L v w) hassoc
    exact ⟨w, Subtype.ext heq.symm⟩

/-- **The factor-place correspondence.** The normalized irreducible factors over `K_v` of the
chosen primitive element's minimal polynomial are in bijection with the places of `L` above `v`. -/
def completionFactorsEquivPlaces :
    completionFactors L v ≃
      {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} :=
  (Equiv.ofBijective (completionFactorOfPlace L v)
    (completionFactorOfPlace_bijective L v)).symm

/-- The factor corresponding to a place under `completionFactorsEquivPlaces` is its completion
factor. -/
@[simp]
theorem completionFactorsEquivPlaces_symm_apply_val
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    ((completionFactorsEquivPlaces L v).symm w).1 = completionFactor L v w :=
  by
    rw [completionFactorsEquivPlaces, Equiv.symm_symm, Equiv.ofBijective_apply]
    rfl

/-- The completion factor of the place corresponding to a factor under
`completionFactorsEquivPlaces` is that factor. -/
@[simp]
theorem completionFactor_completionFactorsEquivPlaces (q : completionFactors L v) :
    completionFactor L v (completionFactorsEquivPlaces L v q) = q.1 := by
  have h := completionFactorsEquivPlaces_symm_apply_val L v
    (completionFactorsEquivPlaces L v q)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

private theorem completionPrimitive_primitive
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    IntermediateField.adjoin (v.adicCompletion K)
      {algebraMap L (w.1.adicCompletion L) (semilocalPowerBasis (K := K) L).gen} = ⊤ := by
  rw [← semilocalPiPowerBasis_gen L v w]
  exact completionFactor_primitive L v w

/-- The canonical map from `L` to a factor field, obtained by sending the chosen primitive
element to the residue class of `X`. -/
def factorFieldAlgHom (q : completionFactors L v) : L →ₐ[K] AdjoinRoot q.1 := by
  apply (semilocalPowerBasis (K := K) L).lift (AdjoinRoot.root q.1)
  rw [← aeval_map_algebraMap (v.adicCompletion K)]
  exact aeval_eq_zero_of_dvd_aeval_eq_zero q.2.2.2 (AdjoinRoot.eval₂_root q.1)

/-- The canonical map to a factor field sends the chosen primitive element to the residue class
of `X`. -/
@[simp]
theorem factorFieldAlgHom_gen (q : completionFactors L v) :
    factorFieldAlgHom L v q (semilocalPowerBasis (K := K) L).gen = AdjoinRoot.root q.1 := by
  simp [factorFieldAlgHom]

/-- **A factor field is the corresponding completion.** For an irreducible factor of the
completed primitive polynomial, quotienting `K_v[X]` by that factor gives the completion `L_w`
at the corresponding place. -/
def factorFieldEquivCompletion (q : completionFactors L v) :
    AdjoinRoot q.1 ≃ₐ[v.adicCompletion K]
      (completionFactorsEquivPlaces L v q).1.adicCompletion L :=
  let w := completionFactorsEquivPlaces L v q
  (AdjoinRoot.algEquivOfEq (v.adicCompletion K) q.1
      (minpoly (v.adicCompletion K)
        (algebraMap L (w.1.adicCompletion L) (semilocalPowerBasis (K := K) L).gen))
      (completionFactor_completionFactorsEquivPlaces L v q).symm).trans
    ((IntermediateField.adjoinRootEquivAdjoin (v.adicCompletion K)
      (IsIntegral.of_finite (v.adicCompletion K)
        (algebraMap L (w.1.adicCompletion L) (semilocalPowerBasis (K := K) L).gen))).trans
      ((IntermediateField.equivOfEq (completionPrimitive_primitive L v w)).trans
        (IntermediateField.topEquiv)))

/-- The factor-field equivalence sends the residue class of `X` to the image of the chosen
primitive generator in the corresponding completion. -/
@[simp]
theorem factorFieldEquivCompletion_root (q : completionFactors L v) :
    factorFieldEquivCompletion L v q (AdjoinRoot.root q.1) =
      algebraMap L ((completionFactorsEquivPlaces L v q).1.adicCompletion L)
        (semilocalPowerBasis (K := K) L).gen := by
  rw [factorFieldEquivCompletion, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AdjoinRoot.algEquivOfEq_root,
    IntermediateField.adjoinRootEquivAdjoin_apply_root]
  rfl

/-- The factor-field/completion equivalence commutes with the canonical maps from `L`. -/
@[simp]
theorem factorFieldEquivCompletion_algebraMap (q : completionFactors L v) (x : L) :
    factorFieldEquivCompletion L v q (factorFieldAlgHom L v q x) =
      algebraMap L ((completionFactorsEquivPlaces L v q).1.adicCompletion L) x := by
  let f : L →ₐ[K] (completionFactorsEquivPlaces L v q).1.adicCompletion L :=
    ((factorFieldEquivCompletion L v q).toAlgHom.restrictScalars K).comp
      (factorFieldAlgHom L v q)
  let g : L →ₐ[K] (completionFactorsEquivPlaces L v q).1.adicCompletion L :=
    IsScalarTower.toAlgHom K L _
  have hfg : f = g := (semilocalPowerBasis (K := K) L).algHom_ext (by
    simp [f, g, factorFieldEquivCompletion_root])
  simpa only [f, g, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    AlgEquiv.toAlgHom_apply, IsScalarTower.toAlgHom_apply] using DFunLike.congr_fun hfg x

private def semilocalFactorHom (q : completionFactors L v) :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] AdjoinRoot q.1 :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (factorFieldAlgHom L v q)
    fun _ _ ↦ .all _ _

/-- The homomorphism assembling the factor-field maps coordinatewise. -/
def semilocalCrtHom :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ((q : completionFactors L v) → AdjoinRoot q.1) :=
  AlgHom.pi fun q ↦ semilocalFactorHom L v q

/-- The product of the factor-field/completion equivalences, reindexed by the
factor-place correspondence. -/
def factorFieldsEquivCompletions :
    ((q : completionFactors L v) → AdjoinRoot q.1) ≃ₐ[v.adicCompletion K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L) :=
  (AlgEquiv.piCongrRight fun q ↦ factorFieldEquivCompletion L v q).trans
    (AlgEquiv.piCongrLeft (v.adicCompletion K)
      (fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
        w.1.adicCompletion L) (completionFactorsEquivPlaces L v))

/-- The product equivalence applies the factor-field equivalence at the factor corresponding to
each place. -/
@[simp]
theorem factorFieldsEquivCompletions_apply
    (x : (q : completionFactors L v) → AdjoinRoot q.1)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    factorFieldsEquivCompletions L v x w =
      (completionFactorsEquivPlaces L v).apply_symm_apply w ▸
        factorFieldEquivCompletion L v ((completionFactorsEquivPlaces L v).symm w)
          (x ((completionFactorsEquivPlaces L v).symm w)) := by
  rw [factorFieldsEquivCompletions, AlgEquiv.trans_apply, AlgEquiv.piCongrLeft_apply,
    Equiv.piCongrLeft_apply]
  rfl

private theorem factorFieldsEquivCompletions_semilocalCrtHom
    (z : v.adicCompletion K ⊗[K] L) :
    factorFieldsEquivCompletions L v (semilocalCrtHom L v z) = semilocalEquiv L v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      ext w
      rw [← (completionFactorsEquivPlaces L v).apply_symm_apply w]
      simp only [factorFieldsEquivCompletions, AlgEquiv.trans_apply,
        AlgEquiv.piCongrLeft_apply, Equiv.piCongrLeft_apply_apply,
        AlgEquiv.piCongrRight_apply, semilocalCrtHom, AlgHom.pi_apply,
        semilocalFactorHom, Algebra.TensorProduct.lift_tmul, semilocalEquiv_tmul]
      rw [map_mul, Algebra.ofId_apply, (factorFieldEquivCompletion L v _).commutes,
        factorFieldEquivCompletion_algebraMap]
  | add x y hx hy => simp [map_add, hx, hy]

/-- **The Chinese remainder assembly.** The scalar extension `K_v ⊗[K] L` is the product of
the quotient fields of the irreducible factors of the completed primitive polynomial: the
semi-local decomposition, read through the factor fields. -/
def semilocalCrtEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ((q : completionFactors L v) → AdjoinRoot q.1) :=
  (semilocalEquiv L v).trans (factorFieldsEquivCompletions L v).symm

/-- The underlying map of the Chinese remainder equivalence is `semilocalCrtHom`. -/
@[simp]
theorem coe_semilocalCrtEquiv : ⇑(semilocalCrtEquiv L v) = semilocalCrtHom L v := by
  funext z
  simp only [semilocalCrtEquiv, AlgEquiv.trans_apply]
  rw [AlgEquiv.symm_apply_eq, factorFieldsEquivCompletions_semilocalCrtHom]

/-- The Chinese remainder equivalence on a pure tensor, evaluated at one factor. -/
@[simp]
theorem semilocalCrtEquiv_tmul (a : v.adicCompletion K) (x : L)
    (q : completionFactors L v) :
    semilocalCrtEquiv L v (a ⊗ₜ x) q =
      algebraMap (v.adicCompletion K) (AdjoinRoot q.1) a * factorFieldAlgHom L v q x := by
  rw [coe_semilocalCrtEquiv]
  simp [semilocalCrtHom, semilocalFactorHom]

/-- **The CRT assembly is the semi-local decomposition.** After identifying every factor field
with its corresponding completion and reindexing factors by places, `semilocalCrtEquiv` agrees
with `semilocalEquiv`. -/
theorem semilocalEquiv_eq_crt :
    semilocalEquiv L v =
      (semilocalCrtEquiv L v).trans (factorFieldsEquivCompletions L v) :=
  AlgEquiv.ext fun z ↦ by
    rw [AlgEquiv.trans_apply, semilocalCrtEquiv, AlgEquiv.trans_apply,
      AlgEquiv.apply_symm_apply]

end TauCeti
