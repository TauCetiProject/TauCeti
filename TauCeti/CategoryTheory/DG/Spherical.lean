/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.CategoryTheory.DG.GradedHomology
public import TauCeti.CategoryTheory.DG.QuasiEquivalence
public import TauCeti.CategoryTheory.DG.Twisted.Shift
public import TauCeti.LinearAlgebra.PerfectPairing.Pi

/-!
# Spherical objects and `A_m`-configurations in differential graded categories

Following Seidel and Thomas (*Braid group actions on derived categories of coherent sheaves*,
Definitions 2.5, 2.9, and 2.15), we formalize `TauCeti.HasFiniteTotalGradedHom` (K2),
`TauCeti.dgTotalHomFinrank`, `TauCeti.dgEulerPairing`, `n`-spherical objects
`TauCeti.IsSphericalObject` (K3–K4, `0 < n`), their invariance under shifted cohomology
equivalences, `H⁰`-isomorphisms, DG quasi-equivalences, and twisted shifts, and
`A_m`-configurations `TauCeti.IsAmSphericalConfiguration`.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*, §2.
-/

public section
noncomputable section

open CategoryTheory HomologicalComplex

namespace TauCeti

universe v u u'

section CommRing

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

private theorem dgHomologyClass_congr {n : ℤ} {X Y : C} {f g : DGHom R n X Y}
    (hf : dgDifferential R n f = 0) (hg : dgDifferential R n g = 0) (h : f = g) :
    dgHomologyClass R f hf = dgHomologyClass R g hg := by cases h; rfl

private def homologyCastEquiv (X Y : C) {a b : ℤ} (hab : a = b) :
    (dgHomComplex R X Y).homology a ≃ₗ[R] (dgHomComplex R X Y).homology b :=
  (eqToIso (congrArg (fun d ↦ (dgHomComplex R X Y).homology d) hab)).toLinearEquiv

private theorem homologyCastEquiv_symm (X Y : C) {a b : ℤ} (hab : a = b) :
    (homologyCastEquiv R X Y hab).symm = homologyCastEquiv R X Y hab.symm := by subst hab; ext; rfl

private theorem homologyCastEquiv_dgHomologyComp {X Y Z : C} {p₁ p₂ q₁ q₂ n₁ n₂ : ℤ}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (hn : n₁ = n₂) (h₁ : p₁ + q₁ = n₁) (h₂ : p₂ + q₂ = n₂)
    (a : (dgHomComplex R X Y).homology p₁) (b : (dgHomComplex R Y Z).homology q₁) :
    homologyCastEquiv R X Z hn (dgHomologyComp R X Y Z h₁ a b) =
      dgHomologyComp R X Y Z h₂ (homologyCastEquiv R X Y hp a) (homologyCastEquiv R Y Z hq b) := by
  subst hp hq hn; rfl

private theorem homotopyIso_exists_classes {X Y : C}
    (e : DGHomotopyCategory.of R X ≅ DGHomotopyCategory.of R Y) :
    ∃ (u : (dgHomComplex R X Y).homology 0) (v : (dgHomComplex R Y X).homology 0),
      dgHomologyComp R X Y X (zero_add 0) u v = dgHomologyId R X ∧
      dgHomologyComp R Y X Y (zero_add 0) v u = dgHomologyId R Y := by
  obtain ⟨f, hf, hfe⟩ := DGHomotopyCategory.exists_homOf_eq R e.hom
  obtain ⟨g, hg, hge⟩ := DGHomotopyCategory.exists_homOf_eq R e.inv
  have hrel {A B : C} {x : DGHom R 0 A B} {y : DGHom R 0 B A}
      (hx : x ∈ dgCycles R A B) (hy : y ∈ dgCycles R B A)
      (h : DGHomotopyCategory.homOf R x hx ≫ DGHomotopyCategory.homOf R y hy =
        𝟙 (DGHomotopyCategory.of R A)) :
      dgHomologyComp R A B A (zero_add 0) (dgHomologyClass R x ((mem_dgCycles R).mp hx))
        (dgHomologyClass R y ((mem_dgCycles R).mp hy)) = dgHomologyId R A := by
    rw [DGHomotopyCategory.homOf_comp, ← DGHomotopyCategory.homOf_dgId,
      DGHomotopyCategory.homOf_eq_iff] at h
    simpa only [dgHomologyComp_zero_eq_dgHomotopyComp, dgHomologyId_def,
      dgHomologyClass_zero_eq_dgHomotopyClass, dgHomotopyComp_dgHomotopyClass,
      dgHomotopyClass_eq_iff] using h
  exact ⟨dgHomologyClass R f ((mem_dgCycles R).mp hf), dgHomologyClass R g ((mem_dgCycles R).mp hg),
    hrel hf hg (by rw [hfe, hge, e.hom_inv_id]), hrel hg hf (by rw [hfe, hge, e.inv_hom_id])⟩

private def gradedPrecompEquiv (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hqp : q + p = 0) (hd₁ : q + d₁ = d₂) (hd₂ : p + d₂ = d₁)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y hqp v u = dgHomologyId R Y) :
    (dgHomComplex R X Z).homology d₁ ≃ₗ[R] (dgHomComplex R Y Z).homology d₂ where
  toFun := dgHomologyComp R Y X Z hd₁ v
  invFun := dgHomologyComp R X Y Z hd₂ u
  left_inv _ := by
    rw [← dgHomologyComp_assoc R hpq hd₁ (zero_add d₁) hd₂, huv, dgHomologyId_dgHomologyComp]
  right_inv _ := by
    rw [← dgHomologyComp_assoc R hqp hd₂ (zero_add d₂) hd₁, hvu, dgHomologyId_dgHomologyComp]
  map_add' := map_add _
  map_smul' := map_smul _

private def gradedPostcompEquiv (Z : C) {X Y : C} {p q d₁ d₂ : ℤ}
    (hpq : p + q = 0) (hqp : q + p = 0) (hd₁ : d₁ + p = d₂) (hd₂ : d₂ + q = d₁)
    (u : (dgHomComplex R X Y).homology p) (v : (dgHomComplex R Y X).homology q)
    (huv : dgHomologyComp R X Y X hpq u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y hqp v u = dgHomologyId R Y) :
    (dgHomComplex R Z X).homology d₁ ≃ₗ[R] (dgHomComplex R Z Y).homology d₂ where
  toFun := (dgHomologyComp R Z X Y hd₁).flip u
  invFun := (dgHomologyComp R Z Y X hd₂).flip v
  left_inv _ := by
    dsimp only [LinearMap.flip_apply]
    rw [dgHomologyComp_assoc R hd₁ hpq hd₂ (add_zero d₁), huv, dgHomologyComp_dgHomologyId]
  right_inv _ := by
    dsimp only [LinearMap.flip_apply]
    rw [dgHomologyComp_assoc R hd₂ hqp hd₁ (add_zero d₂), hvu, dgHomologyComp_dgHomologyId]
  map_add' := map_add _
  map_smul' := map_smul _

/-- Two objects `X` and `Y` of an `R`-linear DG category have **finite total graded `Hom`**
(Seidel–Thomas (K2)) when each `(dgHomComplex R X Y).homology d` is finitely generated and only
finitely many degrees `d : ℤ` are nontrivial. -/
structure HasFiniteTotalGradedHom (X Y : C) : Prop where
  /-- Each graded cohomology group is finitely generated over `R`. -/
  finite (d : ℤ) : Module.Finite R ((dgHomComplex R X Y).homology d)
  /-- Only finitely many cohomological degrees are nontrivial. -/
  bdd_support : {d : ℤ | Nontrivial ((dgHomComplex R X Y).homology d)}.Finite

/-- A finite superset of nontrivial cohomology degrees yields `HasFiniteTotalGradedHom`. -/
theorem HasFiniteTotalGradedHom.of_finset {X Y : C} (s : Finset ℤ)
    [∀ d : ℤ, Module.Finite R ((dgHomComplex R X Y).homology d)]
    (hs : ∀ d ∉ s, Subsingleton ((dgHomComplex R X Y).homology d)) :
    HasFiniteTotalGradedHom R X Y where
  finite _ := inferInstance
  bdd_support := s.finite_toSet.subset fun d hd ↦ by
    by_contra hns; exact @false_of_nontrivial_of_subsingleton _ hd (hs d hns)

variable {R} in
/-- Transport `HasFiniteTotalGradedHom` along degreewise linear equivalences reindexed by `σ`. -/
theorem HasFiniteTotalGradedHom.of_equiv {C' : Type u'} [DGCategory R C']
    {X Y : C} {X' Y' : C'} (h : HasFiniteTotalGradedHom R X Y) (σ : ℤ ≃ ℤ)
    (e : ∀ d : ℤ, (dgHomComplex R X Y).homology (σ d) ≃ₗ[R] (dgHomComplex R X' Y').homology d) :
    HasFiniteTotalGradedHom R X' Y' where
  finite d := by have := h.finite (σ d); exact Module.Finite.equiv (e d)
  bdd_support := (h.bdd_support.preimage σ.injective.injOn).subset fun d hd ↦ by
    have : Nontrivial ((dgHomComplex R X' Y').homology d) := hd
    exact (e d).toEquiv.nontrivial

variable {R} in
/-- Transport `HasFiniteTotalGradedHom` along degree-preserving linear equivalences. -/
theorem HasFiniteTotalGradedHom.of_linearEquiv {C' : Type u'} [DGCategory R C']
    {X Y : C} {X' Y' : C'} (h : HasFiniteTotalGradedHom R X Y)
    (e : ∀ d : ℤ, (dgHomComplex R X Y).homology d ≃ₗ[R] (dgHomComplex R X' Y').homology d) :
    HasFiniteTotalGradedHom R X' Y' :=
  h.of_equiv (Equiv.refl ℤ) e

/-- Infinitely many nontrivial cohomology degrees preclude `HasFiniteTotalGradedHom`. -/
theorem not_hasFiniteTotalGradedHom_of_infinite {X Y : C}
    (h : {d : ℤ | Nontrivial ((dgHomComplex R X Y).homology d)}.Infinite) :
    ¬ HasFiniteTotalGradedHom R X Y := fun hfin ↦ h hfin.bdd_support

/-- Nontrivial cohomology in all even degrees `2 * i` precludes `HasFiniteTotalGradedHom`. -/
theorem not_hasFiniteTotalGradedHom_of_nontrivial_two_mul {X Y : C}
    (h : ∀ i : ℕ, Nontrivial ((dgHomComplex R X Y).homology (2 * (i : ℤ)))) :
    ¬ HasFiniteTotalGradedHom R X Y :=
  not_hasFiniteTotalGradedHom_of_infinite R <|
    Set.infinite_of_injective_forall_mem (fun _ _ (hab : 2 * (_ : ℤ) = 2 * _) ↦ by omega) h

/-- The total graded `Hom` rank `∑ᶠ d : ℤ, Module.finrank R Hom^d(X, Y)`. -/
def dgTotalHomFinrank (X Y : C) : ℕ :=
  ∑ᶠ d : ℤ, Module.finrank R ((dgHomComplex R X Y).homology d)

/-- The graded Euler pairing `χ(X, Y) = ∑ᶠ d : ℤ, (-1)^d * Module.finrank R Hom^d(X, Y)`. -/
def dgEulerPairing (X Y : C) : ℤ :=
  ∑ᶠ d : ℤ, (d.negOnePow : ℤ) * (Module.finrank R ((dgHomComplex R X Y).homology d) : ℤ)

/-- When cohomology vanishes outside `s : Finset ℤ`, `dgTotalHomFinrank` equals the sum over `s`. -/
theorem dgTotalHomFinrank_eq_sum [Nontrivial R] {X Y : C} (s : Finset ℤ)
    (hs : ∀ d ∉ s, Subsingleton ((dgHomComplex R X Y).homology d)) :
    dgTotalHomFinrank R X Y = ∑ d ∈ s, Module.finrank R ((dgHomComplex R X Y).homology d) :=
  finsum_eq_sum_of_support_subset _ fun d hd ↦ by
    by_contra hns; have := hs d hns; exact hd Module.finrank_zero_of_subsingleton

/-- When cohomology vanishes outside `s : Finset ℤ`, `dgEulerPairing` equals the sum over `s`. -/
theorem dgEulerPairing_eq_sum [Nontrivial R] {X Y : C} (s : Finset ℤ)
    (hs : ∀ d ∉ s, Subsingleton ((dgHomComplex R X Y).homology d)) :
    dgEulerPairing R X Y =
      ∑ d ∈ s, (d.negOnePow : ℤ) * (Module.finrank R ((dgHomComplex R X Y).homology d) : ℤ) :=
  finsum_eq_sum_of_support_subset _ fun d hd ↦ by
    by_contra hns; have := hs d hns; exact hd (by simp [Module.finrank_zero_of_subsingleton])

end CommRing

section Field

variable (k : Type v) [Field k] {C : Type u} [DGCategory k C]

/-- An object `E` of a `k`-linear DG category is **`n`-spherical** (Seidel–Thomas, Definition 2.9)
if `0 < n`, `E` has finite total graded `Hom` to every object (K2), `Hom^*(E, E)` has dimension `1`
in degrees `0, n` and `0` elsewhere (K3), and a trace makes composition perfect (K4). -/
structure IsSphericalObject (n : ℤ) (E : C) : Prop where
  /-- Spherical dimension is strictly positive, excluding `0`-spherical dual-number objects. -/
  pos : 0 < n
  /-- Finite total graded `Hom` out of `E` into every object `F` (condition (K2)). -/
  hasFiniteTotalGradedHom_from (F : C) : HasFiniteTotalGradedHom k E F
  /-- Degree-zero cohomology endomorphisms of `E` are one-dimensional (`k · [dgId k E]`). -/
  finrank_homology_zero : Module.finrank k ((dgHomComplex k E E).homology 0) = 1
  /-- Degree-`n` cohomology endomorphisms of `E` are one-dimensional. -/
  finrank_homology_top : Module.finrank k ((dgHomComplex k E E).homology n) = 1
  /-- Cohomology endomorphisms of `E` vanish outside degrees `0` and `n` (condition (K3)). -/
  subsingleton_homology_of_ne {d : ℤ} (hd0 : d ≠ 0) (hdn : d ≠ n) :
    Subsingleton ((dgHomComplex k E E).homology d)
  /-- Existence of a trace functional making composition a perfect pairing in all degrees (K4). -/
  exists_trace_isPerfPair :
    ∃ tr : (dgHomComplex k E E).homology n →ₗ[k] k,
      ∀ (F : C) (d : ℤ), ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr).IsPerfPair

/-- Seidel–Thomas's `n > 0` check: no object is `n`-spherical for `n ≤ 0`. -/
theorem not_isSphericalObject_of_nonpos {n : ℤ} (hn : n ≤ 0) (E : C) :
    ¬ IsSphericalObject k n E := fun hE ↦ (not_lt_of_ge hn) hE.pos

/-- An object violating finite total self-`Hom` in even degrees `2 * i` cannot be `n`-spherical. -/
theorem not_isSphericalObject_of_nontrivial_two_mul (n : ℤ) {E : C}
    (h : ∀ i : ℕ, Nontrivial ((dgHomComplex k E E).homology (2 * (i : ℤ)))) :
    ¬ IsSphericalObject k n E :=
  fun hE ↦ not_hasFiniteTotalGradedHom_of_nontrivial_two_mul k h (hE.hasFiniteTotalGradedHom_from E)

namespace IsSphericalObject

variable {k} {n : ℤ} {E : C}

/-- Every `n`-spherical object has nonzero cohomology identity class `dgHomologyId k E`. -/
theorem dgHomologyId_ne_zero (hE : IsSphericalObject k n E) : dgHomologyId k E ≠ 0 := by
  have := Module.nontrivial_of_finrank_pos (by rw [hE.finrank_homology_zero]; exact Nat.one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : (dgHomComplex k E E).homology 0)
  intro hid; apply hx
  rw [← dgHomologyId_dgHomologyComp k x, hid, map_zero, LinearMap.zero_apply]

/-- `Hom^0(E, E)` of an `n`-spherical object is spanned by `dgHomologyId k E`. -/
theorem span_dgHomologyId_eq_top (hE : IsSphericalObject k n E) :
    Submodule.span k {dgHomologyId k E} = ⊤ := by
  have := (hE.hasFiniteTotalGradedHom_from E).finite 0
  exact Submodule.eq_top_of_finrank_eq <|
    (finrank_span_singleton hE.dgHomologyId_ne_zero).trans hE.finrank_homology_zero.symm

/-- Serre duality (K4) implies finite total graded `Hom` into an `n`-spherical object `E`. -/
theorem hasFiniteTotalGradedHom_to (hE : IsSphericalObject k n E) (F : C) :
    HasFiniteTotalGradedHom k F E := by
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  refine (hE.hasFiniteTotalGradedHom_from F).of_equiv (Equiv.subLeft n) fun d ↦ ?_
  have := (hE.hasFiniteTotalGradedHom_from F).finite (n - d); have := htr F (n - d)
  exact ((LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm).trans
    (((dgHomologyComp k E F E (add_sub_cancel (n - d) n)).compr₂ tr).flip).toPerfPair.symm).trans
    (homologyCastEquiv k F E (sub_sub_self n d))

/-- Complementary cohomology groups `Hom^d(E, F)` and `Hom^{n - d}(F, E)` have equal `finrank`. -/
theorem finrank_homology_symm (hE : IsSphericalObject k n E) (F : C) (d : ℤ) :
    Module.finrank k ((dgHomComplex k F E).homology (n - d)) =
      Module.finrank k ((dgHomComplex k E F).homology d) := by
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair; have := htr F d
  exact (((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr).flip).toPerfPair.finrank_eq
    |>.trans Subspace.dual_finrank_eq

/-- Total graded `Hom` dimensions into and out of an `n`-spherical object coincide. -/
theorem dgTotalHomFinrank_symm (hE : IsSphericalObject k n E) (F : C) :
    dgTotalHomFinrank k F E = dgTotalHomFinrank k E F := by
  rw [dgTotalHomFinrank, dgTotalHomFinrank, ← finsum_comp_equiv (Equiv.subLeft n)
    (f := fun d ↦ Module.finrank k ((dgHomComplex k F E).homology d))]
  exact finsum_congr fun d ↦ hE.finrank_homology_symm F d

/-- Every witnessing trace functional of an `n`-spherical object is nonzero. -/
theorem trace_ne_zero (hE : IsSphericalObject k n E)
    {tr : (dgHomComplex k E E).homology n →ₗ[k] k}
    (htr : ∀ (F : C) (d : ℤ),
      ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr).IsPerfPair) : tr ≠ 0 := by
  have := Module.nontrivial_of_finrank_pos (by rw [hE.finrank_homology_top]; exact Nat.one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : (dgHomComplex k E E).homology n)
  rintro rfl; have := htr E n
  exact hx <| (LinearMap.IsPerfPair.bijective_left
    ((dgHomologyComp k E E E (add_sub_cancel n n)).compr₂ 0)).injective <| LinearMap.ext fun _ ↦ rfl

/-- Because `Hom^n(E, E)` is one-dimensional, **every** nonzero functional
`tr' : Hom^n(E, E) →ₗ[k] k` makes composition a perfect pairing for an `n`-spherical object `E`. -/
theorem isPerfPair_of_trace_ne_zero (hE : IsSphericalObject k n E)
    {tr' : (dgHomComplex k E E).homology n →ₗ[k] k} (htr' : tr' ≠ 0) (F : C) (d : ℤ) :
    ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr').IsPerfPair := by
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' tr (hE.trace_ne_zero htr)).mp
    (Subspace.dual_finrank_eq.trans hE.finrank_homology_top) tr'
  have hc0 : c ≠ 0 := by rintro rfl; exact htr' (by rw [← hc, zero_smul])
  have := htr F d
  convert LinearMap.IsPerfPair.smul_of_isUnit hc0.isUnit
    ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr)
  ext a b; simp [← hc]

private theorem subsingleton_not_mem_pair (hE : IsSphericalObject k n E) {d : ℤ}
    (hd : d ∉ ({0, n} : Finset ℤ)) : Subsingleton ((dgHomComplex k E E).homology d) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  exact hE.subsingleton_homology_of_ne hd.1 hd.2

/-- An `n`-spherical object has total graded endomorphism dimension `2`. -/
theorem dgTotalHomFinrank_self (hE : IsSphericalObject k n E) : dgTotalHomFinrank k E E = 2 := by
  rw [dgTotalHomFinrank_eq_sum k ({0, n} : Finset ℤ) fun _ ↦ hE.subsingleton_not_mem_pair,
    Finset.sum_pair (ne_of_lt hE.pos), hE.finrank_homology_zero, hE.finrank_homology_top]

/-- The self-Euler pairing of an `n`-spherical object is `1 + (-1)^n`. -/
theorem dgEulerPairing_self (hE : IsSphericalObject k n E) :
    dgEulerPairing k E E = 1 + (n.negOnePow : ℤ) := by
  rw [dgEulerPairing_eq_sum k ({0, n} : Finset ℤ) fun _ ↦ hE.subsingleton_not_mem_pair,
    Finset.sum_pair (ne_of_lt hE.pos), hE.finrank_homology_zero, hE.finrank_homology_top]
  simp

/-- Every even-dimensional spherical object has self-Euler pairing `2`. -/
theorem dgEulerPairing_self_of_even (hE : IsSphericalObject k n E) (hn : Even n) :
    dgEulerPairing k E E = 2 := by
  rw [hE.dgEulerPairing_self, Int.negOnePow_even _ hn, Units.val_one]; norm_num

private theorem of_gradedPair {E' : C} (hE : IsSphericalObject k n E) {p q : ℤ}
    (hpq : p + q = 0) (hqp : q + p = 0)
    (u : (dgHomComplex k E E').homology p) (v : (dgHomComplex k E' E).homology q)
    (huv : dgHomologyComp k E E' E hpq u v = dgHomologyId k E)
    (hvu : dgHomologyComp k E' E E' hqp v u = dgHomologyId k E') :
    IsSphericalObject k n E' := by
  let eLeft (F : C) (d : ℤ) :=
    gradedPrecompEquiv k F hpq hqp (by omega : q + (p + d) = d) rfl u v huv hvu
  let eRight (F : C) (d : ℤ) :=
    gradedPostcompEquiv k F hpq hqp (by omega : (d + q) + p = d) rfl u v huv hvu
  let eEnd (d : ℤ) := (homologyCastEquiv k E E (by omega : d = (p + d) + q)).trans
    ((eRight E (p + d)).trans (eLeft E' d))
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  refine ⟨hE.pos,
    fun F ↦ (hE.hasFiniteTotalGradedHom_from F).of_equiv (Equiv.addLeft p) (eLeft F),
    (eEnd 0).symm.finrank_eq.trans hE.finrank_homology_zero,
    (eEnd n).symm.finrank_eq.trans hE.finrank_homology_top,
    fun hd0 hdn ↦ by
      have := hE.subsingleton_homology_of_ne hd0 hdn
      exact (eEnd _).toEquiv.subsingleton_congr.mp inferInstance,
    ⟨tr.comp (eEnd n).symm.toLinearMap, fun F d ↦ ?_⟩⟩
  have := htr F (p + d)
  convert (inferInstance :
    (((dgHomologyComp k E F E (add_sub_cancel (p + d) n)).compr₂ tr).compl₁₂
      (eLeft F d).symm.toLinearMap
      ((eRight F (n - d)).symm.trans
        (homologyCastEquiv k F E (by omega : n - d + q = n - (p + d)))).toLinearMap).IsPerfPair)
  ext a b
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe, eEnd, eLeft, eRight, gradedPrecompEquiv, gradedPostcompEquiv,
    LinearEquiv.symm_trans_apply, LinearEquiv.trans_apply, LinearEquiv.coe_symm_mk,
    LinearMap.flip_apply]
  apply congrArg tr
  rw [← dgHomologyComp_assoc k (pq := p + d) rfl (add_sub_cancel d n) (by omega) rfl u a b,
    dgHomologyComp_assoc k (qr := n - d + q) (by omega) rfl rfl (by omega) _ b v,
    homologyCastEquiv_symm]
  exact homologyCastEquiv_dgHomologyComp k rfl (by omega : n - d + q = n - (p + d))
    (by omega : (p + n) + q = n) (by omega) (add_sub_cancel (p + d) n) _ _

/-- A mutually inverse pair of cohomology classes `u ∈ Hom^{-m}(E, E')` and `v ∈ Hom^m(E', E)`
transports `n`-sphericality from `E` to `E'`. -/
theorem of_gradedEquiv {E' : C} (hE : IsSphericalObject k n E) {m : ℤ}
    (u : (dgHomComplex k E E').homology (-m)) (v : (dgHomComplex k E' E).homology m)
    (huv : dgHomologyComp k E E' E (neg_add_cancel m) u v = dgHomologyId k E)
    (hvu : dgHomologyComp k E' E E' (add_neg_cancel m) v u = dgHomologyId k E') :
    IsSphericalObject k n E' :=
  hE.of_gradedPair (neg_add_cancel m) (add_neg_cancel m) u v huv hvu

/-- Isomorphic objects in `DGHomotopyCategory k C` have equivalent `n`-sphericality. -/
theorem of_homotopyIso {E' : C} (hE : IsSphericalObject k n E)
    (e : DGHomotopyCategory.of k E ≅ DGHomotopyCategory.of k E') : IsSphericalObject k n E' := by
  obtain ⟨u, v, huv, hvu⟩ := homotopyIso_exists_classes k e
  exact hE.of_gradedPair (zero_add 0) (zero_add 0) u v huv hvu

end IsSphericalObject

/-- A sequence `E : Fin m → C` is an **`A_m`-configuration of `n`-spherical objects**
(Seidel–Thomas, Definition 2.15) if each `E i` is `n`-spherical and, for distinct `i ≠ j`, the
total graded `Hom` space between `E i` and `E j` has dimension `1` when `|i - j| = 1` and `0`
otherwise. -/
structure IsAmSphericalConfiguration (m : ℕ) (n : ℤ) (E : Fin m → C) : Prop where
  /-- Every object in the configuration is `n`-spherical. -/
  isSphericalObject (i : Fin m) : IsSphericalObject k n (E i)
  /-- Adjacent objects in the `A_m` chain have one-dimensional total graded `Hom`. -/
  dgTotalHomFinrank_of_adj {i j : Fin m}
    (hadj : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) : dgTotalHomFinrank k (E i) (E j) = 1
  /-- Distinct nonadjacent objects in the `A_m` chain have zero total graded `Hom`. -/
  dgTotalHomFinrank_of_nonadj {i j : Fin m} (hne : i ≠ j)
    (hnadj : ¬ ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ))) :
    dgTotalHomFinrank k (E i) (E j) = 0

end Field

namespace DGTwistedObject

variable {k : Type v} [Field k] {C : Type u} [DGCategory k C]

/-- Shifting a twisted complex by `m : ℤ` preserves and reflects `n`-sphericality. -/
@[simp]
theorem isSphericalObject_shiftFunctor_iff (n m : ℤ)
    (P : DGTwistedObject k (DGAdditiveClosure (DGShiftClosure C))) :
    IsSphericalObject k n ((shiftFunctor k m).obj P) ↔ IsSphericalObject k n P := by
  let u := dgHomologyClass k (toShift P m) (dgDifferential_toShift P m)
  let v := dgHomologyClass k (fromShift P m) (dgDifferential_fromShift P m)
  have huv : dgHomologyComp k P ((shiftFunctor k m).obj P) P (neg_add_cancel m) u v =
      dgHomologyId k P := by
    rw [dgHomologyComp_dgHomologyClass, dgHomologyId_def]
    exact dgHomologyClass_congr k _ _ (dgComp_toShift_fromShift P m)
  have hvu : dgHomologyComp k ((shiftFunctor k m).obj P) P ((shiftFunctor k m).obj P)
      (add_neg_cancel m) v u = dgHomologyId k ((shiftFunctor k m).obj P) := by
    rw [dgHomologyComp_dgHomologyClass, dgHomologyId_def]
    exact dgHomologyClass_congr k _ _ (dgComp_fromShift_toShift P m)
  exact ⟨fun hPm ↦ hPm.of_gradedPair (add_neg_cancel m) (neg_add_cancel m) v u hvu huv,
    fun hP ↦ hP.of_gradedPair (neg_add_cancel m) (add_neg_cancel m) u v huv hvu⟩

end DGTwistedObject

end TauCeti

namespace CategoryTheory.EnrichedFunctor

open TauCeti HomologicalComplex

universe v u₁ u₂

section CommRing

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂} [DGCategory R C] [DGCategory R D]
  {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}

/-- A quasi-fully faithful DG functor induces linear equivalences on all Hom cohomology groups. -/
def IsQuasiFullyFaithful.homologyLinearEquiv (hF : F.IsQuasiFullyFaithful) (X Y : C) (d : ℤ) :
    (dgHomComplex R X Y).homology d ≃ₗ[R] (dgHomComplex R (F.obj X) (F.obj Y)).homology d :=
  have := hF.isIso_homologyMap X Y d
  (asIso (homologyMap (F.map X Y) d)).toLinearEquiv

/-- `IsQuasiFullyFaithful.homologyLinearEquiv` acts via `HomologicalComplex.homologyMap`. -/
@[simp]
theorem IsQuasiFullyFaithful.homologyLinearEquiv_apply (hF : F.IsQuasiFullyFaithful)
    (X Y : C) (d : ℤ) (x : (dgHomComplex R X Y).homology d) :
    hF.homologyLinearEquiv X Y d x = (homologyMap (F.map X Y) d).hom x := (rfl)

/-- `IsQuasiFullyFaithful.homologyLinearEquiv` commutes with graded cohomology composition. -/
theorem IsQuasiFullyFaithful.homologyLinearEquiv_dgHomologyComp (hF : F.IsQuasiFullyFaithful)
    {X Y Z : C} {p q n : ℤ} (hpq : p + q = n)
    (x : (dgHomComplex R X Y).homology p) (y : (dgHomComplex R Y Z).homology q) :
    hF.homologyLinearEquiv X Z n (dgHomologyComp R X Y Z hpq x y) =
      dgHomologyComp R (F.obj X) (F.obj Y) (F.obj Z) hpq
        (hF.homologyLinearEquiv X Y p x) (hF.homologyLinearEquiv Y Z q y) :=
  F.homologyMap_dgHomologyComp hpq x y

end CommRing

section Field

variable {k : Type v} [Field k] {C : Type u₁} {D : Type u₂} [DGCategory k C] [DGCategory k D]
  {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} k) ℤ) C D}

private theorem isSphericalObject_of_map (hff : F.IsQuasiFullyFaithful) {n : ℤ} {E : C}
    (hFE : IsSphericalObject k n (F.obj E)) : IsSphericalObject k n E := by
  obtain ⟨tr, htr⟩ := hFE.exists_trace_isPerfPair
  refine ⟨hFE.pos,
    fun X ↦ (hFE.hasFiniteTotalGradedHom_from (F.obj X)).of_linearEquiv
      fun d ↦ (hff.homologyLinearEquiv E X d).symm,
    (hff.homologyLinearEquiv E E 0).finrank_eq.trans hFE.finrank_homology_zero,
    (hff.homologyLinearEquiv E E n).finrank_eq.trans hFE.finrank_homology_top,
    fun hd0 hdn ↦ by
      have := hFE.subsingleton_homology_of_ne hd0 hdn
      exact (hff.homologyLinearEquiv E E _).toEquiv.subsingleton_congr.mpr inferInstance,
    ⟨tr.comp (hff.homologyLinearEquiv E E n).toLinearMap, fun X d ↦ ?_⟩⟩
  have := htr (F.obj X) d
  convert (inferInstance :
    (((dgHomologyComp k (F.obj E) (F.obj X) (F.obj E) (add_sub_cancel d n)).compr₂ tr).compl₁₂
      (hff.homologyLinearEquiv E X d).toLinearMap
      (hff.homologyLinearEquiv X E (n - d)).toLinearMap).IsPerfPair)
  ext a b; simp [hff.homologyLinearEquiv_dgHomologyComp]

/-- A DG quasi-equivalence preserves and reflects `n`-spherical objects. -/
theorem IsQuasiEquivalence.isSphericalObject_iff (hF : F.IsQuasiEquivalence) (n : ℤ) (E : C) :
    IsSphericalObject k n (F.obj E) ↔ IsSphericalObject k n E := by
  have hff := hF.isQuasiFullyFaithful
  refine ⟨isSphericalObject_of_map hff, fun hE ↦ ?_⟩
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  refine ⟨hE.pos, fun Y ↦ ?_,
    (hff.homologyLinearEquiv E E 0).symm.finrank_eq.trans hE.finrank_homology_zero,
    (hff.homologyLinearEquiv E E n).symm.finrank_eq.trans hE.finrank_homology_top,
    fun hd0 hdn ↦ by
      have := hE.subsingleton_homology_of_ne hd0 hdn
      exact (hff.homologyLinearEquiv E E _).toEquiv.subsingleton_congr.mp inferInstance,
    ⟨tr.comp (hff.homologyLinearEquiv E E n).symm.toLinearMap, fun Y d ↦ ?_⟩⟩
  · obtain ⟨X, ⟨eY⟩⟩ := hF.essentiallySurjective Y
    obtain ⟨u, v, huv, hvu⟩ := TauCeti.homotopyIso_exists_classes k eY
    exact ((hE.hasFiniteTotalGradedHom_from X).of_linearEquiv
      (hff.homologyLinearEquiv E X)).of_linearEquiv fun d ↦
      TauCeti.gradedPostcompEquiv k (F.obj E) (zero_add 0) (zero_add 0) (add_zero d) (add_zero d)
        u v huv hvu
  · obtain ⟨X, ⟨eY⟩⟩ := hF.essentiallySurjective Y
    obtain ⟨u, v, huv, hvu⟩ := TauCeti.homotopyIso_exists_classes k eY
    let eL := (TauCeti.gradedPostcompEquiv k (F.obj E) (zero_add 0) (zero_add 0)
      (add_zero d) (add_zero d) u v huv hvu).symm.trans (hff.homologyLinearEquiv E X d).symm
    let eR := (TauCeti.gradedPrecompEquiv k (F.obj E) (zero_add 0) (zero_add 0)
      (zero_add (n - d)) (zero_add (n - d)) u v huv hvu).symm.trans
      (hff.homologyLinearEquiv X E (n - d)).symm
    have := htr X d
    convert (inferInstance :
      (((dgHomologyComp k E X E (add_sub_cancel d n)).compr₂ tr).compl₁₂
        eL.toLinearMap eR.toLinearMap).IsPerfPair)
    ext a b
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₁₂_apply,
      LinearEquiv.coe_coe]
    apply congrArg tr; apply (hff.homologyLinearEquiv E E n).injective
    rw [LinearEquiv.apply_symm_apply, hff.homologyLinearEquiv_dgHomologyComp]
    simp only [eL, eR, TauCeti.gradedPostcompEquiv, TauCeti.gradedPrecompEquiv,
      LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.coe_symm_mk,
      LinearMap.flip_apply]
    rw [dgHomologyComp_assoc k (add_zero d) (zero_add (n - d)) (add_sub_cancel d n)
        (add_sub_cancel d n),
      ← dgHomologyComp_assoc k (zero_add 0) (zero_add (n - d)) (zero_add (n - d))
        (zero_add (n - d)),
      hvu, dgHomologyId_dgHomologyComp]

end Field

end CategoryTheory.EnrichedFunctor
