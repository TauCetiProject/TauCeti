/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic

/-!
# Partially semialgebraic sets

Write points of `E × (ι → ℝ)` as `(u, x)`, with *base point* `u` in a real normed space `E` and
*fibre coordinates* `x`. Following Łojasiewicz, a set `s ⊆ E × (ι → ℝ)` is *partially
semialgebraic* (with respect to the fibre coordinates) if every base point `u₀` has a neighbourhood
`U` such that, over `U`, the set `s` is a finite Boolean combination of the zero sets and positivity
sets of functions `(u, x) ↦ ∑ₘ aₘ(u) xᵐ` that are polynomial in `x` with coefficients `aₘ` analytic
on `U`. The neighbourhood is taken in the base only: the description holds on the whole cylinder
`U × (ι → ℝ)`, so it is semialgebraic in the fibre direction, uniformly over `U`.

In Łojasiewicz's triangulation of semianalytic sets this class controls the vertical direction:
bounded semianalytic sets with a nonsingular vertical direction are shown there to be partially
semialgebraic, through their local Weierstrass polynomial descriptions, and property (A) of the
triangulating homeomorphism asks that its graph be partially semialgebraic with respect to the
source coordinates. This file develops the closure properties that follow directly from the
definition; closure under projection along the fibre needs quantifier elimination with
parameters and is not proved here.

## Main declarations

* `TauCeti.IsAnalyticCoeffPolynomialOn U f`: `f (u, x)` is a polynomial in `x` with coefficients
  analytic on `U`.
* `TauCeti.IsAnalyticCoeffBooleanCombination U t`: `t` is a finite Boolean combination of the zero
  sets and positivity sets of such functions.
* `TauCeti.PartiallySemialgebraicAt s u`: `s` is partially semialgebraic over the base point `u`.
* `TauCeti.IsPartiallySemialgebraic s`: `s` is partially semialgebraic over every base point.

## Main results

* Finite Boolean operations: `TauCeti.isSetAlgebra_setOf_partiallySemialgebraicAt` and
  `TauCeti.isSetAlgebra_setOf_isPartiallySemialgebraic`, with the named consequences, and
  `LocallyFinite.isPartiallySemialgebraic_iUnion` for families whose projections to the base are
  locally finite.
* `TauCeti.PartiallySemialgebraicAt.exists_subset`: a presentation exists over every sufficiently
  small neighbourhood of the base point.
* `TauCeti.PartiallySemialgebraicAt.preimage_prodMap` and
  `TauCeti.IsPartiallySemialgebraic.preimage_prodMap`: preimages under analytic changes of the
  base.
* `TauCeti.IsSemianalytic.isPartiallySemialgebraic_preimage_fst` and
  `TauCeti.IsSemialgebraic.isPartiallySemialgebraic_preimage_snd`: cylinders over semianalytic sets
  of the base and over semialgebraic sets of the fibre are partially semialgebraic.
* `TauCeti.IsPartiallySemialgebraic.isSemialgebraic_preimage_prodMk`: every fibre of a partially
  semialgebraic set is semialgebraic.
* `TauCeti.IsPartiallySemialgebraic.isSemianalytic`: partially semialgebraic sets are semianalytic.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §1, for partially semialgebraic sets and their closure properties.
-/

public section

open Filter MeasureTheory MvPolynomial Set Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*}

/-! ### Polynomials in the fibre with analytic coefficients -/

/-- A function `f : E × (ι → ℝ) → ℝ` is a *polynomial in the fibre with coefficients analytic on
`U`* if `f (u, x) = ∑ₘ aₘ(u) xᵐ` for finitely many real functions `aₘ` analytic on `U`. The
polynomial is recorded as `P : MvPolynomial ι (E → ℝ)`, evaluated at `(u, x)` by evaluating its
coefficients at `u` and its variables at `x`. -/
def IsAnalyticCoeffPolynomialOn (U : Set E) (f : E × (ι → ℝ) → ℝ) : Prop :=
  ∃ P : MvPolynomial ι (E → ℝ), (∀ m, AnalyticOnNhd ℝ (P.coeff m) U) ∧
    ∀ p, f p = P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) p.1) p.2

/-- A function is a polynomial in the fibre with coefficients analytic on `U` if and only if it is
the evaluation of a polynomial whose coefficients are analytic on `U`. -/
theorem isAnalyticCoeffPolynomialOn_def {U : Set E} {f : E × (ι → ℝ) → ℝ} :
    IsAnalyticCoeffPolynomialOn U f ↔ ∃ P : MvPolynomial ι (E → ℝ),
      (∀ m, AnalyticOnNhd ℝ (P.coeff m) U) ∧
        ∀ p, f p = P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) p.1) p.2 :=
  Iff.rfl

/-- The evaluation of a polynomial whose coefficients are analytic on `U` is a polynomial in the
fibre with coefficients analytic on `U`. -/
theorem isAnalyticCoeffPolynomialOn_eval₂ {U : Set E} (P : MvPolynomial ι (E → ℝ))
    (hP : ∀ m, AnalyticOnNhd ℝ (P.coeff m) U) :
    IsAnalyticCoeffPolynomialOn U fun p => P.eval₂ (Pi.evalRingHom (fun _ : E => ℝ) p.1) p.2 :=
  ⟨P, hP, fun _ => rfl⟩

/-- A function of the base point alone, analytic on `U`, is a polynomial in the fibre (of degree
zero) with coefficients analytic on `U`. -/
theorem _root_.AnalyticOnNhd.isAnalyticCoeffPolynomialOn_comp_fst {U : Set E} {a : E → ℝ}
    (ha : AnalyticOnNhd ℝ a U) :
    IsAnalyticCoeffPolynomialOn (ι := ι) U fun p => a p.1 := by
  classical
  refine ⟨C a, fun m => ?_, fun p => by simp⟩
  rw [coeff_C]
  split_ifs
  exacts [ha, analyticOnNhd_const]

/-- A real polynomial in the fibre coordinates alone is a polynomial in the fibre with coefficients
analytic on every set. -/
theorem isAnalyticCoeffPolynomialOn_eval_snd (U : Set E) (q : MvPolynomial ι ℝ) :
    IsAnalyticCoeffPolynomialOn U fun p : E × (ι → ℝ) => eval p.2 q := by
  refine ⟨q.map (algebraMap ℝ (E → ℝ)), fun m => ?_, fun p => ?_⟩
  · rw [coeff_map, Pi.algebraMap_def]
    exact analyticOnNhd_const
  · have h : (Pi.evalRingHom (fun _ : E => ℝ) p.1).comp (algebraMap ℝ (E → ℝ)) = RingHom.id ℝ :=
      RingHom.ext fun _ => by simp
    rw [eval₂_map, h, eval₂_id]

namespace IsAnalyticCoeffPolynomialOn

variable {U V : Set E} {f : E × (ι → ℝ) → ℝ}

/-- A polynomial in the fibre with coefficients analytic on `U` also has coefficients analytic on
every smaller set. -/
theorem mono (hf : IsAnalyticCoeffPolynomialOn U f) (hVU : V ⊆ U) :
    IsAnalyticCoeffPolynomialOn V f :=
  let ⟨P, hP, hfP⟩ := hf
  ⟨P, fun m => (hP m).mono hVU, hfP⟩

/-- Precomposing a polynomial in the fibre with an analytic change `g` of the base point, which maps
`V` into `U`, gives a polynomial in the fibre with coefficients analytic on `V`. -/
theorem comp_prodMap (hf : IsAnalyticCoeffPolynomialOn U f) {V : Set F} {g : F → E}
    (hg : AnalyticOnNhd ℝ g V) (hgVU : MapsTo g V U) :
    IsAnalyticCoeffPolynomialOn V (f ∘ Prod.map g id) := by
  obtain ⟨P, hP, hfP⟩ := hf
  let φ : (E → ℝ) →+* (F → ℝ) := RingHom.pi fun y => Pi.evalRingHom (fun _ : E => ℝ) (g y)
  refine ⟨P.map φ, fun m => ?_, fun p => ?_⟩
  · rw [coeff_map]
    exact (hP m).comp hg hgVU
  · have h : (Pi.evalRingHom (fun _ : F => ℝ) p.1).comp φ =
        Pi.evalRingHom (fun _ : E => ℝ) (Prod.map g id p).1 :=
      RingHom.ext fun _ => by simp [φ]
    rw [eval₂_map, h, Function.comp_apply, hfP, Prod.map_snd, id_eq]

/-- Over a fixed base point `u`, a polynomial in the fibre is a real polynomial in the fibre
coordinates. -/
theorem exists_eval_eq (hf : IsAnalyticCoeffPolynomialOn U f) (u : E) :
    ∃ q : MvPolynomial ι ℝ, ∀ x, f (u, x) = eval x q := by
  obtain ⟨P, -, hfP⟩ := hf
  exact ⟨P.map (Pi.evalRingHom (fun _ : E => ℝ) u), fun x => by rw [hfP, eval_map]⟩

/-- A polynomial in the fibre with coefficients analytic on `U` is analytic on the cylinder
`U × (ι → ℝ)`. -/
theorem analyticOnNhd [Fintype ι] (hf : IsAnalyticCoeffPolynomialOn U f) :
    AnalyticOnNhd ℝ f (Prod.fst ⁻¹' U) := by
  obtain ⟨P, hP, hfP⟩ := hf
  have hfP' : f = ∑ d ∈ P.support, fun p => P.coeff d p.1 * ∏ i, p.2 i ^ d i := by
    ext p
    simp only [Finset.sum_apply, hfP, eval₂_eq', Pi.evalRingHom_apply]
  rw [hfP']
  refine Finset.analyticOnNhd_sum _ fun d _ p hp => ?_
  have hcoord (i : ι) : AnalyticAt ℝ (fun q : E × (ι → ℝ) => q.2 i) p :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).analyticAt _).comp analyticAt_snd
  exact ((hP d p.1 hp).comp analyticAt_fst).mul
    (Finset.analyticAt_fun_prod _ fun i _ => (hcoord i).pow _)

end IsAnalyticCoeffPolynomialOn

/-! ### Finite Boolean combinations -/

/-- A set `t ⊆ E × (ι → ℝ)` is a *finite Boolean combination of analytic-coefficient polynomial
sign conditions on `U`* if it belongs to the algebra of sets generated by the zero sets
`{p | f p = 0}` and the positivity sets `{p | 0 < f p}` of the polynomials `f` in the fibre with
coefficients analytic on `U`. Only the part of `t` over `U` is meaningful. -/
def IsAnalyticCoeffBooleanCombination (U : Set E) (t : Set (E × (ι → ℝ))) : Prop :=
  t ∈ generateSetAlgebra
    ({t | ∃ f, IsAnalyticCoeffPolynomialOn U f ∧ t = {p | f p = 0}} ∪
      {t | ∃ f, IsAnalyticCoeffPolynomialOn U f ∧ t = {p | 0 < f p}})

/-- A set is a finite Boolean combination of analytic-coefficient polynomial sign conditions on `U`
if and only if it belongs to the algebra of sets generated by the zero sets and positivity sets of
the polynomials in the fibre with coefficients analytic on `U`. -/
theorem isAnalyticCoeffBooleanCombination_def {U : Set E} {t : Set (E × (ι → ℝ))} :
    IsAnalyticCoeffBooleanCombination U t ↔ t ∈ generateSetAlgebra
      ({t | ∃ f, IsAnalyticCoeffPolynomialOn U f ∧ t = {p | f p = 0}} ∪
        {t | ∃ f, IsAnalyticCoeffPolynomialOn U f ∧ t = {p | 0 < f p}}) :=
  Iff.rfl

/-- The zero set of a polynomial in the fibre with coefficients analytic on `U` is a Boolean
combination of analytic-coefficient polynomial sign conditions on `U`. -/
theorem IsAnalyticCoeffPolynomialOn.isAnalyticCoeffBooleanCombination_setOf_eq_zero {U : Set E}
    {f : E × (ι → ℝ) → ℝ} (hf : IsAnalyticCoeffPolynomialOn U f) :
    IsAnalyticCoeffBooleanCombination U {p | f p = 0} :=
  self_subset_generateSetAlgebra (Or.inl ⟨f, hf, rfl⟩)

/-- The positivity set of a polynomial in the fibre with coefficients analytic on `U` is a Boolean
combination of analytic-coefficient polynomial sign conditions on `U`. -/
theorem IsAnalyticCoeffPolynomialOn.isAnalyticCoeffBooleanCombination_setOf_pos {U : Set E}
    {f : E × (ι → ℝ) → ℝ} (hf : IsAnalyticCoeffPolynomialOn U f) :
    IsAnalyticCoeffBooleanCombination U {p | 0 < f p} :=
  self_subset_generateSetAlgebra (Or.inr ⟨f, hf, rfl⟩)

variable (ι) in
/-- The finite Boolean combinations of analytic-coefficient polynomial sign conditions on `U` form
an algebra of sets. -/
theorem isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination (U : Set E) :
    IsSetAlgebra {t : Set (E × (ι → ℝ)) | IsAnalyticCoeffBooleanCombination U t} :=
  isSetAlgebra_generateSetAlgebra

/-- The finite Boolean combinations of analytic-coefficient polynomial sign conditions on `U` form
the smallest algebra of sets containing the zero set and the positivity set of every polynomial in
the fibre with coefficients analytic on `U`. -/
theorem setOf_isAnalyticCoeffBooleanCombination_subset {U : Set E}
    {ℬ : Set (Set (E × (ι → ℝ)))} (hℬ : IsSetAlgebra ℬ)
    (eq_zero : ∀ f, IsAnalyticCoeffPolynomialOn U f → {p | f p = 0} ∈ ℬ)
    (pos : ∀ f, IsAnalyticCoeffPolynomialOn U f → {p | 0 < f p} ∈ ℬ) :
    {t | IsAnalyticCoeffBooleanCombination U t} ⊆ ℬ :=
  hℬ.generateSetAlgebra_subset <| union_subset (fun _ ⟨f, hf, h⟩ => h ▸ eq_zero f hf)
    (fun _ ⟨f, hf, h⟩ => h ▸ pos f hf)

/-- The empty set is a Boolean combination of analytic-coefficient polynomial sign conditions. -/
@[simp]
theorem isAnalyticCoeffBooleanCombination_empty (U : Set E) :
    IsAnalyticCoeffBooleanCombination U (∅ : Set (E × (ι → ℝ))) :=
  (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).empty_mem

/-- The whole space is a Boolean combination of analytic-coefficient polynomial sign conditions. -/
@[simp]
theorem isAnalyticCoeffBooleanCombination_univ (U : Set E) :
    IsAnalyticCoeffBooleanCombination U (univ : Set (E × (ι → ℝ))) :=
  (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).univ_mem

namespace IsAnalyticCoeffBooleanCombination

variable {U V : Set E} {t t' : Set (E × (ι → ℝ))}

/-- The complement of a Boolean combination of analytic-coefficient polynomial sign conditions is
one. -/
theorem compl (ht : IsAnalyticCoeffBooleanCombination U t) :
    IsAnalyticCoeffBooleanCombination U tᶜ :=
  (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).compl_mem ht

/-- The union of two Boolean combinations of analytic-coefficient polynomial sign conditions is
one. -/
theorem union (ht : IsAnalyticCoeffBooleanCombination U t)
    (ht' : IsAnalyticCoeffBooleanCombination U t') :
    IsAnalyticCoeffBooleanCombination U (t ∪ t') :=
  (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).union_mem ht ht'

/-- The intersection of two Boolean combinations of analytic-coefficient polynomial sign conditions
is one. -/
theorem inter (ht : IsAnalyticCoeffBooleanCombination U t)
    (ht' : IsAnalyticCoeffBooleanCombination U t') :
    IsAnalyticCoeffBooleanCombination U (t ∩ t') :=
  (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).inter_mem ht ht'

/-- The difference of two Boolean combinations of analytic-coefficient polynomial sign conditions
is one. -/
theorem sdiff (ht : IsAnalyticCoeffBooleanCombination U t)
    (ht' : IsAnalyticCoeffBooleanCombination U t') :
    IsAnalyticCoeffBooleanCombination U (t \ t') :=
  (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).sdiff_mem ht ht'

/-- A finite union of Boolean combinations of analytic-coefficient polynomial sign conditions is
one. -/
protected theorem biUnion {κ : Type*} {I : Set κ} (hI : I.Finite) {t : κ → Set (E × (ι → ℝ))}
    (ht : ∀ i ∈ I, IsAnalyticCoeffBooleanCombination U (t i)) :
    IsAnalyticCoeffBooleanCombination U (⋃ i ∈ I, t i) := by
  simpa using (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).biUnion_mem
    hI.toFinset fun i hi => ht i (hI.mem_toFinset.1 hi)

/-- A finite intersection of Boolean combinations of analytic-coefficient polynomial sign
conditions is one. -/
protected theorem biInter {κ : Type*} {I : Set κ} (hI : I.Finite) {t : κ → Set (E × (ι → ℝ))}
    (ht : ∀ i ∈ I, IsAnalyticCoeffBooleanCombination U (t i)) :
    IsAnalyticCoeffBooleanCombination U (⋂ i ∈ I, t i) := by
  simpa using (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).biInter_mem
    hI.toFinset fun i hi => ht i (hI.mem_toFinset.1 hi)

/-- A Boolean combination of analytic-coefficient polynomial sign conditions on `U` is also one on
every smaller set `V ⊆ U`. -/
theorem mono (ht : IsAnalyticCoeffBooleanCombination U t) (hVU : V ⊆ U) :
    IsAnalyticCoeffBooleanCombination V t :=
  setOf_isAnalyticCoeffBooleanCombination_subset
    (isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι V)
    (fun _ hf => (hf.mono hVU).isAnalyticCoeffBooleanCombination_setOf_eq_zero)
    (fun _ hf => (hf.mono hVU).isAnalyticCoeffBooleanCombination_setOf_pos) ht

/-- The preimage of a Boolean combination of analytic-coefficient polynomial sign conditions on `U`
under an analytic change `g` of the base point, which maps `V` into `U`, is a Boolean combination of
analytic-coefficient polynomial sign conditions on `V`. -/
theorem preimage_prodMap (ht : IsAnalyticCoeffBooleanCombination U t) {V : Set F} {g : F → E}
    (hg : AnalyticOnNhd ℝ g V) (hgVU : MapsTo g V U) :
    IsAnalyticCoeffBooleanCombination V (Prod.map g id ⁻¹' t) :=
  setOf_isAnalyticCoeffBooleanCombination_subset
    ((isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι V).preimage (Prod.map g id))
    (fun _ hf => (hf.comp_prodMap hg hgVU).isAnalyticCoeffBooleanCombination_setOf_eq_zero)
    (fun _ hf => (hf.comp_prodMap hg hgVU).isAnalyticCoeffBooleanCombination_setOf_pos) ht

/-- Over a fixed base point `u`, a Boolean combination of analytic-coefficient polynomial sign
conditions is a semialgebraic subset of the fibre. -/
theorem isSemialgebraic_preimage_prodMk (ht : IsAnalyticCoeffBooleanCombination U t) (u : E) :
    IsSemialgebraic (Prod.mk u ⁻¹' t) := by
  refine setOf_isAnalyticCoeffBooleanCombination_subset
    (isSetAlgebra_setOf_isSemialgebraic.preimage (Prod.mk u)) (fun f hf => ?_) (fun f hf => ?_) ht
  all_goals
    obtain ⟨q, hq⟩ := hf.exists_eval_eq u
    simp only [mem_ofPred_eq, preimage_ofPred_eq, hq]
  exacts [isSemialgebraic_eval_eq_zero q, isSemialgebraic_eval_pos q]

/-- A Boolean combination of analytic-coefficient polynomial sign conditions on `U` is a Boolean
combination of analytic sign conditions on the cylinder `U × (ι → ℝ)`. -/
theorem isAnalyticBooleanCombination [Fintype ι] (ht : IsAnalyticCoeffBooleanCombination U t) :
    IsAnalyticBooleanCombination (Prod.fst ⁻¹' U) t :=
  setOf_isAnalyticCoeffBooleanCombination_subset
    (isSetAlgebra_setOf_isAnalyticBooleanCombination _)
    (fun _ hf => isAnalyticBooleanCombination_setOf_eq_zero hf.analyticOnNhd)
    (fun _ hf => isAnalyticBooleanCombination_setOf_pos hf.analyticOnNhd) ht

/-- **Sign-condition normal form.** A Boolean combination of analytic-coefficient polynomial sign
conditions on `U` is described by a condition on the signs of finitely many polynomials in the
fibre with coefficients analytic on `U`. -/
theorem exists_eq_setOf_sign (ht : IsAnalyticCoeffBooleanCombination U t) :
    ∃ (m : ℕ) (f : Fin m → E × (ι → ℝ) → ℝ), (∀ i, IsAnalyticCoeffPolynomialOn U (f i)) ∧
      ∃ Φ : (Fin m → SignType) → Prop, t = {p | Φ fun i => SignType.sign (f i p)} :=
  exists_eq_setOf_sign_of_mem_generateSetAlgebra ht

end IsAnalyticCoeffBooleanCombination

/-- The cylinder over a Boolean combination of analytic sign conditions on `U` in the base is a
Boolean combination of analytic-coefficient polynomial sign conditions on `U`. -/
theorem IsAnalyticBooleanCombination.isAnalyticCoeffBooleanCombination_preimage_fst {U t : Set E}
    (ht : IsAnalyticBooleanCombination U t) :
    IsAnalyticCoeffBooleanCombination U (Prod.fst ⁻¹' t : Set (E × (ι → ℝ))) :=
  setOf_isAnalyticBooleanCombination_subset
    ((isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).preimage Prod.fst)
    (fun _ ha =>
      ha.isAnalyticCoeffPolynomialOn_comp_fst.isAnalyticCoeffBooleanCombination_setOf_eq_zero)
    (fun _ ha =>
      ha.isAnalyticCoeffPolynomialOn_comp_fst.isAnalyticCoeffBooleanCombination_setOf_pos)
    ht

/-- The cylinder over a semialgebraic subset of the fibre is a Boolean combination of
analytic-coefficient polynomial sign conditions on every set. -/
theorem IsSemialgebraic.isAnalyticCoeffBooleanCombination_preimage_snd {t : Set (ι → ℝ)}
    (ht : IsSemialgebraic t) (U : Set E) :
    IsAnalyticCoeffBooleanCombination U (Prod.snd ⁻¹' t : Set (E × (ι → ℝ))) :=
  setOf_isSemialgebraic_subset
    ((isSetAlgebra_setOf_isAnalyticCoeffBooleanCombination ι U).preimage Prod.snd)
    (fun q =>
      (isAnalyticCoeffPolynomialOn_eval_snd U q).isAnalyticCoeffBooleanCombination_setOf_eq_zero)
    (fun q =>
      (isAnalyticCoeffPolynomialOn_eval_snd U q).isAnalyticCoeffBooleanCombination_setOf_pos)
    ht

/-! ### Partial semialgebraicity over a base point -/

/-- A set `s ⊆ E × (ι → ℝ)` is *partially semialgebraic over* the base point `u` if, over some
neighbourhood `U` of `u`, it agrees with a finite Boolean combination of zero sets and positivity
sets of polynomials in the fibre with coefficients analytic on `U`. The agreement holds on the whole
cylinder `U × (ι → ℝ)`. -/
def PartiallySemialgebraicAt (s : Set (E × (ι → ℝ))) (u : E) : Prop :=
  ∃ U ∈ 𝓝 u, ∃ t, IsAnalyticCoeffBooleanCombination U t ∧
    s ∩ Prod.fst ⁻¹' U = t ∩ Prod.fst ⁻¹' U

/-- A set is partially semialgebraic over `u` if and only if, over some neighbourhood `U` of `u`,
it agrees with a finite Boolean combination of analytic-coefficient polynomial sign conditions
on `U`. -/
theorem partiallySemialgebraicAt_def {s : Set (E × (ι → ℝ))} {u : E} :
    PartiallySemialgebraicAt s u ↔ ∃ U ∈ 𝓝 u, ∃ t, IsAnalyticCoeffBooleanCombination U t ∧
      s ∩ Prod.fst ⁻¹' U = t ∩ Prod.fst ⁻¹' U :=
  Iff.rfl

section PartiallySemialgebraicAt

variable {s s' : Set (E × (ι → ℝ))} {u : E}

/-- **Shrinking invariance.** If `s` is partially semialgebraic over `u`, then it has a
presentation over a neighbourhood of `u` inside any prescribed neighbourhood `V` of `u`. -/
theorem PartiallySemialgebraicAt.exists_subset (hs : PartiallySemialgebraicAt s u) {V : Set E}
    (hV : V ∈ 𝓝 u) :
    ∃ U ∈ 𝓝 u, U ⊆ V ∧ ∃ t, IsAnalyticCoeffBooleanCombination U t ∧
      s ∩ Prod.fst ⁻¹' U = t ∩ Prod.fst ⁻¹' U := by
  obtain ⟨U, hU, t, ht, hst⟩ := hs
  refine ⟨U ∩ V, inter_mem hU hV, inter_subset_right, t, ht.mono inter_subset_left, ?_⟩
  rw [preimage_inter, ← inter_assoc, hst, inter_assoc]

/-- Being partially semialgebraic over `u` only depends on the part of the set over a
neighbourhood of `u`. -/
theorem PartiallySemialgebraicAt.congr (hs : PartiallySemialgebraicAt s u) {V : Set E}
    (hV : V ∈ 𝓝 u) (h : s ∩ Prod.fst ⁻¹' V = s' ∩ Prod.fst ⁻¹' V) :
    PartiallySemialgebraicAt s' u := by
  obtain ⟨U, hU, hUV, t, ht, hst⟩ := hs.exists_subset hV
  refine ⟨U, hU, t, ht, ?_⟩
  have hUV' : Prod.fst ⁻¹' U ⊆ (Prod.fst ⁻¹' V : Set (E × (ι → ℝ))) := preimage_mono hUV
  rw [← hst, ← inter_eq_right.2 hUV', ← inter_assoc, ← inter_assoc, h]

variable (ι) in
/-- The sets partially semialgebraic over a base point form an algebra of sets. -/
theorem isSetAlgebra_setOf_partiallySemialgebraicAt (u : E) :
    IsSetAlgebra {s : Set (E × (ι → ℝ)) | PartiallySemialgebraicAt s u} where
  empty_mem := ⟨univ, univ_mem, ∅, isAnalyticCoeffBooleanCombination_empty univ, by simp⟩
  compl_mem := by
    rintro s ⟨U, hU, t, ht, hst⟩
    refine ⟨U, hU, tᶜ, ht.compl, ?_⟩
    ext p
    have := Set.ext_iff.1 hst p
    simp only [mem_inter_iff, mem_compl_iff] at this ⊢
    tauto
  union_mem := by
    rintro s s' hs ⟨U', hU', t', ht', hst'⟩
    obtain ⟨U, hU, hUU', t, ht, hst⟩ := hs.exists_subset hU'
    refine ⟨U, hU, t ∪ t', ht.union (ht'.mono hUU'), ?_⟩
    ext p
    have h₁ := Set.ext_iff.1 hst p
    have h₂ := Set.ext_iff.1 hst' p
    have h₃ := @hUU' p.1
    simp only [mem_inter_iff, mem_union, mem_preimage] at h₁ h₂ ⊢
    tauto

/-- The empty set is partially semialgebraic over every base point. -/
@[simp]
theorem partiallySemialgebraicAt_empty : PartiallySemialgebraicAt (∅ : Set (E × (ι → ℝ))) u :=
  (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).empty_mem

/-- The whole space is partially semialgebraic over every base point. -/
@[simp]
theorem partiallySemialgebraicAt_univ : PartiallySemialgebraicAt (univ : Set (E × (ι → ℝ))) u :=
  (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).univ_mem

/-- The complement of a set partially semialgebraic over `u` is partially semialgebraic over
`u`. -/
theorem PartiallySemialgebraicAt.compl (hs : PartiallySemialgebraicAt s u) :
    PartiallySemialgebraicAt sᶜ u :=
  (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).compl_mem hs

/-- A set is partially semialgebraic over `u` if and only if its complement is. -/
@[simp]
theorem partiallySemialgebraicAt_compl_iff :
    PartiallySemialgebraicAt sᶜ u ↔ PartiallySemialgebraicAt s u :=
  ⟨fun hs => compl_compl s ▸ hs.compl, PartiallySemialgebraicAt.compl⟩

/-- The union of two sets partially semialgebraic over `u` is partially semialgebraic over `u`. -/
theorem PartiallySemialgebraicAt.union (hs : PartiallySemialgebraicAt s u)
    (hs' : PartiallySemialgebraicAt s' u) : PartiallySemialgebraicAt (s ∪ s') u :=
  (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).union_mem hs hs'

/-- The intersection of two sets partially semialgebraic over `u` is partially semialgebraic over
`u`. -/
theorem PartiallySemialgebraicAt.inter (hs : PartiallySemialgebraicAt s u)
    (hs' : PartiallySemialgebraicAt s' u) : PartiallySemialgebraicAt (s ∩ s') u :=
  (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).inter_mem hs hs'

/-- The difference of two sets partially semialgebraic over `u` is partially semialgebraic over
`u`. -/
theorem PartiallySemialgebraicAt.sdiff (hs : PartiallySemialgebraicAt s u)
    (hs' : PartiallySemialgebraicAt s' u) : PartiallySemialgebraicAt (s \ s') u :=
  (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).sdiff_mem hs hs'

/-- A finite union of sets partially semialgebraic over `u` is partially semialgebraic over `u`. -/
theorem PartiallySemialgebraicAt.biUnion {κ : Type*} {I : Set κ} (hI : I.Finite)
    {s : κ → Set (E × (ι → ℝ))} (hs : ∀ i ∈ I, PartiallySemialgebraicAt (s i) u) :
    PartiallySemialgebraicAt (⋃ i ∈ I, s i) u := by
  simpa using (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).biUnion_mem hI.toFinset
    fun i hi => hs i (hI.mem_toFinset.1 hi)

/-- A finite intersection of sets partially semialgebraic over `u` is partially semialgebraic over
`u`. -/
theorem PartiallySemialgebraicAt.biInter {κ : Type*} {I : Set κ} (hI : I.Finite)
    {s : κ → Set (E × (ι → ℝ))} (hs : ∀ i ∈ I, PartiallySemialgebraicAt (s i) u) :
    PartiallySemialgebraicAt (⋂ i ∈ I, s i) u := by
  simpa using (isSetAlgebra_setOf_partiallySemialgebraicAt ι u).biInter_mem hI.toFinset
    fun i hi => hs i (hI.mem_toFinset.1 hi)

/-- **Analytic changes of the base.** If `s` is partially semialgebraic over `g y` and `g` is
analytic on a neighbourhood `W` of `y`, then `Prod.map g id ⁻¹' s` is partially semialgebraic over
`y`. -/
theorem PartiallySemialgebraicAt.preimage_prodMap {g : F → E} {y : F} {W : Set F}
    (hs : PartiallySemialgebraicAt s (g y)) (hW : W ∈ 𝓝 y) (hg : AnalyticOnNhd ℝ g W) :
    PartiallySemialgebraicAt (Prod.map g id ⁻¹' s) y := by
  obtain ⟨U, hU, t, ht, hst⟩ := hs
  refine ⟨W ∩ g ⁻¹' U,
    inter_mem hW ((hg y (mem_of_mem_nhds hW)).continuousAt.preimage_mem_nhds hU), _,
    ht.preimage_prodMap (hg.mono inter_subset_left) fun _ hz => hz.2, ?_⟩
  have h := congrArg (Prod.map g id ⁻¹' ·) hst
  simp only [preimage_inter] at h
  ext p
  have hp := Set.ext_iff.1 h p
  simp only [mem_inter_iff, mem_preimage, Prod.map_fst] at hp ⊢
  tauto

/-- Over a base point `u` where `s` is partially semialgebraic, the fibre `{x | (u, x) ∈ s}` is a
semialgebraic set. -/
theorem PartiallySemialgebraicAt.isSemialgebraic_preimage_prodMk
    (hs : PartiallySemialgebraicAt s u) : IsSemialgebraic (Prod.mk u ⁻¹' s) := by
  obtain ⟨U, hU, t, ht, hst⟩ := hs
  have hU' : Prod.mk u ⁻¹' (Prod.fst ⁻¹' U) = (univ : Set (ι → ℝ)) := by
    ext x
    simp [mem_of_mem_nhds hU]
  have h := congrArg (Prod.mk u ⁻¹' ·) hst
  simp only [preimage_inter, hU', inter_univ] at h
  exact h ▸ ht.isSemialgebraic_preimage_prodMk u

/-- A set partially semialgebraic over `u` is semianalytic at every point `(u, x)` over `u`. -/
theorem PartiallySemialgebraicAt.semianalyticAt [Fintype ι] (hs : PartiallySemialgebraicAt s u)
    (x : ι → ℝ) : SemianalyticAt s (u, x) := by
  obtain ⟨U, hU, t, ht, hst⟩ := hs
  exact semianalyticAt_def.2 ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt.preimage_mem_nhds hU, t,
    ht.isAnalyticBooleanCombination, hst⟩

/-- The cylinder over a set semianalytic at `u` is partially semialgebraic over `u`. -/
theorem SemianalyticAt.partiallySemialgebraicAt_preimage_fst {s : Set E}
    (hs : SemianalyticAt s u) :
    PartiallySemialgebraicAt (Prod.fst ⁻¹' s : Set (E × (ι → ℝ))) u := by
  obtain ⟨U, hU, t, ht, hst⟩ := semianalyticAt_def.1 hs
  refine ⟨U, hU, _, ht.isAnalyticCoeffBooleanCombination_preimage_fst, ?_⟩
  rw [← preimage_inter, hst, preimage_inter]

/-- The cylinder over a semialgebraic subset of the fibre is partially semialgebraic over every base
point. -/
theorem IsSemialgebraic.partiallySemialgebraicAt_preimage_snd {t : Set (ι → ℝ)}
    (ht : IsSemialgebraic t) (u : E) :
    PartiallySemialgebraicAt (Prod.snd ⁻¹' t : Set (E × (ι → ℝ))) u :=
  ⟨univ, univ_mem, _, ht.isAnalyticCoeffBooleanCombination_preimage_snd univ, rfl⟩

end PartiallySemialgebraicAt

/-! ### Partially semialgebraic sets -/

/-- A set `s ⊆ E × (ι → ℝ)` is *partially semialgebraic* if it is partially semialgebraic over
every base point: over a neighbourhood `U` of every point of `E`, it agrees with a finite Boolean
combination of zero sets and positivity sets of polynomials in the fibre coordinates with
coefficients analytic on `U`. -/
def IsPartiallySemialgebraic (s : Set (E × (ι → ℝ))) : Prop :=
  ∀ u, PartiallySemialgebraicAt s u

/-- A set is partially semialgebraic if and only if it is partially semialgebraic over every base
point. -/
theorem isPartiallySemialgebraic_iff {s : Set (E × (ι → ℝ))} :
    IsPartiallySemialgebraic s ↔ ∀ u, PartiallySemialgebraicAt s u :=
  Iff.rfl

/-- A partially semialgebraic set is partially semialgebraic over every base point. -/
theorem IsPartiallySemialgebraic.partiallySemialgebraicAt {s : Set (E × (ι → ℝ))}
    (hs : IsPartiallySemialgebraic s) (u : E) : PartiallySemialgebraicAt s u :=
  hs u

/-- The zero set of a polynomial in the fibre with coefficients analytic on `E` is partially
semialgebraic. -/
theorem IsAnalyticCoeffPolynomialOn.isPartiallySemialgebraic_setOf_eq_zero
    {f : E × (ι → ℝ) → ℝ} (hf : IsAnalyticCoeffPolynomialOn univ f) :
    IsPartiallySemialgebraic {p | f p = 0} :=
  fun _ => ⟨univ, univ_mem, _, hf.isAnalyticCoeffBooleanCombination_setOf_eq_zero, rfl⟩

/-- The positivity set of a polynomial in the fibre with coefficients analytic on `E` is partially
semialgebraic. -/
theorem IsAnalyticCoeffPolynomialOn.isPartiallySemialgebraic_setOf_pos
    {f : E × (ι → ℝ) → ℝ} (hf : IsAnalyticCoeffPolynomialOn univ f) :
    IsPartiallySemialgebraic {p | 0 < f p} :=
  fun _ => ⟨univ, univ_mem, _, hf.isAnalyticCoeffBooleanCombination_setOf_pos, rfl⟩

variable (E ι) in
/-- The partially semialgebraic sets form an algebra of sets. -/
theorem isSetAlgebra_setOf_isPartiallySemialgebraic :
    IsSetAlgebra {s : Set (E × (ι → ℝ)) | IsPartiallySemialgebraic s} where
  empty_mem _ := partiallySemialgebraicAt_empty
  compl_mem _ hs u := (hs u).compl
  union_mem _ _ hs hs' u := (hs u).union (hs' u)

/-- The empty set is partially semialgebraic. -/
@[simp]
theorem isPartiallySemialgebraic_empty : IsPartiallySemialgebraic (∅ : Set (E × (ι → ℝ))) :=
  (isSetAlgebra_setOf_isPartiallySemialgebraic E ι).empty_mem

/-- The whole space is partially semialgebraic. -/
@[simp]
theorem isPartiallySemialgebraic_univ : IsPartiallySemialgebraic (univ : Set (E × (ι → ℝ))) :=
  (isSetAlgebra_setOf_isPartiallySemialgebraic E ι).univ_mem

namespace IsPartiallySemialgebraic

variable {s s' : Set (E × (ι → ℝ))}

/-- The complement of a partially semialgebraic set is partially semialgebraic. -/
protected theorem compl (hs : IsPartiallySemialgebraic s) : IsPartiallySemialgebraic sᶜ :=
  fun u => (hs u).compl

/-- The union of two partially semialgebraic sets is partially semialgebraic. -/
protected theorem union (hs : IsPartiallySemialgebraic s) (hs' : IsPartiallySemialgebraic s') :
    IsPartiallySemialgebraic (s ∪ s') :=
  fun u => (hs u).union (hs' u)

/-- The intersection of two partially semialgebraic sets is partially semialgebraic. -/
protected theorem inter (hs : IsPartiallySemialgebraic s) (hs' : IsPartiallySemialgebraic s') :
    IsPartiallySemialgebraic (s ∩ s') :=
  fun u => (hs u).inter (hs' u)

/-- The difference of two partially semialgebraic sets is partially semialgebraic. -/
protected theorem sdiff (hs : IsPartiallySemialgebraic s) (hs' : IsPartiallySemialgebraic s') :
    IsPartiallySemialgebraic (s \ s') :=
  fun u => (hs u).sdiff (hs' u)

/-- A finite union of partially semialgebraic sets is partially semialgebraic. -/
protected theorem biUnion {κ : Type*} {I : Set κ} (hI : I.Finite) {s : κ → Set (E × (ι → ℝ))}
    (hs : ∀ i ∈ I, IsPartiallySemialgebraic (s i)) : IsPartiallySemialgebraic (⋃ i ∈ I, s i) :=
  fun u => .biUnion hI fun i hi => hs i hi u

/-- A finite intersection of partially semialgebraic sets is partially semialgebraic. -/
protected theorem biInter {κ : Type*} {I : Set κ} (hI : I.Finite) {s : κ → Set (E × (ι → ℝ))}
    (hs : ∀ i ∈ I, IsPartiallySemialgebraic (s i)) : IsPartiallySemialgebraic (⋂ i ∈ I, s i) :=
  fun u => .biInter hI fun i hi => hs i hi u

/-- The union of a finite family of partially semialgebraic sets is partially semialgebraic. -/
protected theorem iUnion {κ : Type*} [Finite κ] {s : κ → Set (E × (ι → ℝ))}
    (hs : ∀ i, IsPartiallySemialgebraic (s i)) : IsPartiallySemialgebraic (⋃ i, s i) := by
  simpa using IsPartiallySemialgebraic.biUnion finite_univ fun i (_ : i ∈ univ) => hs i

/-- The intersection of a finite family of partially semialgebraic sets is partially
semialgebraic. -/
protected theorem iInter {κ : Type*} [Finite κ] {s : κ → Set (E × (ι → ℝ))}
    (hs : ∀ i, IsPartiallySemialgebraic (s i)) : IsPartiallySemialgebraic (⋂ i, s i) := by
  simpa using IsPartiallySemialgebraic.biInter finite_univ fun i (_ : i ∈ univ) => hs i

/-- **Analytic changes of the base.** The preimage of a partially semialgebraic set under
`Prod.map g id`, for a real analytic map `g` of the bases, is partially semialgebraic. -/
protected theorem preimage_prodMap (hs : IsPartiallySemialgebraic s) {g : F → E}
    (hg : AnalyticOnNhd ℝ g univ) : IsPartiallySemialgebraic (Prod.map g id ⁻¹' s) :=
  fun y => (hs (g y)).preimage_prodMap univ_mem hg

/-- Every fibre `{x | (u, x) ∈ s}` of a partially semialgebraic set is semialgebraic. -/
theorem isSemialgebraic_preimage_prodMk (hs : IsPartiallySemialgebraic s) (u : E) :
    IsSemialgebraic (Prod.mk u ⁻¹' s) :=
  (hs u).isSemialgebraic_preimage_prodMk

/-- A partially semialgebraic set is semianalytic. -/
theorem isSemianalytic [Fintype ι] (hs : IsPartiallySemialgebraic s) : IsSemianalytic s :=
  isSemianalytic_iff.2 fun p => (hs p.1).semianalyticAt p.2

end IsPartiallySemialgebraic

/-- A set is partially semialgebraic if and only if its complement is. -/
@[simp]
theorem isPartiallySemialgebraic_compl_iff {s : Set (E × (ι → ℝ))} :
    IsPartiallySemialgebraic sᶜ ↔ IsPartiallySemialgebraic s :=
  forall_congr' fun _ => partiallySemialgebraicAt_compl_iff

/-- **Locally finite unions.** The union of a family of partially semialgebraic sets whose
projections to the base form a locally finite family is partially semialgebraic. -/
theorem _root_.LocallyFinite.isPartiallySemialgebraic_iUnion {κ : Type*}
    {s : κ → Set (E × (ι → ℝ))} (hfin : LocallyFinite fun i => Prod.fst '' s i)
    (hs : ∀ i, IsPartiallySemialgebraic (s i)) : IsPartiallySemialgebraic (⋃ i, s i) := by
  intro u
  obtain ⟨V, hV, hI⟩ := hfin u
  refine (PartiallySemialgebraicAt.biUnion hI fun i _ => hs i u).congr hV ?_
  ext p
  simp only [mem_inter_iff, mem_iUnion, mem_preimage, exists_prop]
  exact ⟨fun ⟨⟨i, _, hpi⟩, hp⟩ => ⟨⟨i, hpi⟩, hp⟩,
    fun ⟨⟨i, hpi⟩, hp⟩ => ⟨⟨i, ⟨p.1, ⟨p, hpi, rfl⟩, hp⟩, hpi⟩, hp⟩⟩

/-- The cylinder over a semianalytic subset of the base is partially semialgebraic. -/
theorem IsSemianalytic.isPartiallySemialgebraic_preimage_fst {s : Set E} (hs : IsSemianalytic s) :
    IsPartiallySemialgebraic (Prod.fst ⁻¹' s : Set (E × (ι → ℝ))) :=
  fun u => (hs.semianalyticAt u).partiallySemialgebraicAt_preimage_fst

/-- The cylinder over a semialgebraic subset of the fibre is partially semialgebraic. -/
theorem IsSemialgebraic.isPartiallySemialgebraic_preimage_snd {t : Set (ι → ℝ)}
    (ht : IsSemialgebraic t) : IsPartiallySemialgebraic (Prod.snd ⁻¹' t : Set (E × (ι → ℝ))) :=
  ht.partiallySemialgebraicAt_preimage_snd

end TauCeti
