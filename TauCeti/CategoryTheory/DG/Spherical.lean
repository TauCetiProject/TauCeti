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

Let `C` be a differential graded category over a field `k`. Following Seidel and Thomas
(*Braid group actions on derived categories of coherent sheaves*, Definitions 2.5, 2.9, and 2.15),
we formalize the cohomological finiteness, sphericality, and configuration predicates on objects
of `C` using Mathlib's canonical cohomology `(dgHomComplex k X Y).homology d` and the graded
composition `TauCeti.dgHomologyComp`.

## Main definitions and results

* `TauCeti.HasFiniteTotalGradedHom`: Seidel–Thomas condition (K2) requiring every cohomology space
  `(dgHomComplex R X Y).homology d` to be finitely generated and only finitely many degrees `d : ℤ`
  to be nontrivial. Mere degreewise finiteness does not suffice when infinitely many degrees are
  nonzero (`TauCeti.not_hasFiniteTotalGradedHom_of_nontrivial_two_mul`).
* `TauCeti.dgTotalHomFinrank` and `TauCeti.dgEulerPairing`: total graded `Hom` dimension
  `∑ᶠ d, finrank Hom^d(X, Y)` and graded Euler form `∑ᶠ d, (-1)^d finrank Hom^d(X, Y)`.
* `TauCeti.IsSphericalObject`: an `n`-spherical object `E` (`0 < n`) has finite total graded `Hom`
  to every object, `Hom^*(E, E)` concentrated in degrees `0` and `n` of dimension `1` each (K3),
  and a trace `Hom^n(E, E) →ₗ[k] k` making composition a perfect pairing in all complementary
  degrees `(d, n - d)` against every object `F` (K4).
* Invariance of `TauCeti.IsSphericalObject` under shifted cohomology equivalences
  (`TauCeti.IsSphericalObject.of_gradedEquiv`), `H⁰`-isomorphisms, DG quasi-equivalences
  (`CategoryTheory.EnrichedFunctor.IsQuasiEquivalence.isSphericalObject_iff`), and shifts of
  twisted complexes (`TauCeti.DGTwistedObject.isSphericalObject_shiftFunctor_iff`).
* `TauCeti.IsAmSphericalConfiguration`: an `A_m`-configuration `Fin m → C` of `n`-spherical objects
  whose total graded `Hom` between distinct objects has dimension `1` at distance `1` and `0`
  otherwise.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*,
  Definitions 2.5, 2.9, and 2.15.
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
    dgHomologyClass R f hf = dgHomologyClass R g hg := by
  cases h
  rfl

private def homologyCastEquiv (X Y : C) {a b : ℤ} (hab : a = b) :
    (dgHomComplex R X Y).homology a ≃ₗ[R] (dgHomComplex R X Y).homology b :=
  (eqToIso (congrArg (fun d ↦ (dgHomComplex R X Y).homology d) hab)).toLinearEquiv

private theorem homologyCastEquiv_symm (X Y : C) {a b : ℤ} (hab : a = b) :
    (homologyCastEquiv R X Y hab).symm = homologyCastEquiv R X Y hab.symm := by
  subst hab
  ext x
  rfl

private theorem dgDifferential_castDeg_eq_zero {X Y : C} {a b : ℤ} (hab : a = b)
    {f : DGHom R a X Y} (hf : dgDifferential R a f = 0) :
    dgDifferential R b (castDeg R hab f) = 0 := by
  subst hab
  simpa only [castDeg_self] using hf

private theorem homologyCastEquiv_dgHomologyClass {X Y : C} {a b : ℤ} (hab : a = b)
    (f : DGHom R a X Y) (hf : dgDifferential R a f = 0) :
    homologyCastEquiv R X Y hab (dgHomologyClass R f hf) =
      dgHomologyClass R (castDeg R hab f) (dgDifferential_castDeg_eq_zero R hab hf) := by
  subst hab
  exact dgHomologyClass_congr R hf _ (castDeg_self R rfl f).symm

private theorem homotopyIso_exists_classes {X Y : C}
    (e : DGHomotopyCategory.of R X ≅ DGHomotopyCategory.of R Y) :
    ∃ (u : (dgHomComplex R X Y).homology 0) (v : (dgHomComplex R Y X).homology 0),
      dgHomologyComp R X Y X (zero_add 0) u v = dgHomologyId R X ∧
      dgHomologyComp R Y X Y (zero_add 0) v u = dgHomologyId R Y := by
  obtain ⟨f, hf, hfe⟩ := DGHomotopyCategory.exists_homOf_eq R e.hom
  obtain ⟨g, hg, hge⟩ := DGHomotopyCategory.exists_homOf_eq R e.inv
  have hf0 : dgDifferential R 0 f = 0 := (mem_dgCycles R).mp hf
  have hg0 : dgDifferential R 0 g = 0 := (mem_dgCycles R).mp hg
  refine ⟨dgHomologyClass R f hf0, dgHomologyClass R g hg0, ?_, ?_⟩
  · have h := e.hom_inv_id
    rw [← hfe, ← hge, DGHomotopyCategory.homOf_comp, ← DGHomotopyCategory.homOf_dgId,
      DGHomotopyCategory.homOf_eq_iff] at h
    rw [dgHomologyComp_zero_eq_dgHomotopyComp, dgHomologyId_def,
      dgHomologyClass_zero_eq_dgHomotopyClass, dgHomologyClass_zero_eq_dgHomotopyClass,
      dgHomologyClass_zero_eq_dgHomotopyClass, dgHomotopyComp_dgHomotopyClass,
      dgHomotopyClass_eq_iff]
    exact h
  · have h := e.inv_hom_id
    rw [← hfe, ← hge, DGHomotopyCategory.homOf_comp, ← DGHomotopyCategory.homOf_dgId,
      DGHomotopyCategory.homOf_eq_iff] at h
    rw [dgHomologyComp_zero_eq_dgHomotopyComp, dgHomologyId_def,
      dgHomologyClass_zero_eq_dgHomotopyClass, dgHomologyClass_zero_eq_dgHomotopyClass,
      dgHomologyClass_zero_eq_dgHomotopyClass, dgHomotopyComp_dgHomotopyClass,
      dgHomotopyClass_eq_iff]
    exact h

private def homotopyPostcompEquiv (Z : C) {X Y : C}
    (u : (dgHomComplex R X Y).homology 0) (v : (dgHomComplex R Y X).homology 0)
    (huv : dgHomologyComp R X Y X (zero_add 0) u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y (zero_add 0) v u = dgHomologyId R Y) (d : ℤ) :
    (dgHomComplex R Z X).homology d ≃ₗ[R] (dgHomComplex R Z Y).homology d where
  toFun := (dgHomologyComp R Z X Y (add_zero d)).flip u
  invFun := (dgHomologyComp R Z Y X (add_zero d)).flip v
  left_inv a := by
    dsimp only [LinearMap.flip_apply]
    rw [dgHomologyComp_assoc R (add_zero d) (zero_add 0) (add_zero d) (add_zero d),
      huv, dgHomologyComp_dgHomologyId]
  right_inv a := by
    dsimp only [LinearMap.flip_apply]
    rw [dgHomologyComp_assoc R (add_zero d) (zero_add 0) (add_zero d) (add_zero d),
      hvu, dgHomologyComp_dgHomologyId]
  map_add' := map_add _
  map_smul' := map_smul _

private theorem homotopyPostcompEquiv_symm_apply (Z : C) {X Y : C}
    (u : (dgHomComplex R X Y).homology 0) (v : (dgHomComplex R Y X).homology 0)
    (huv : dgHomologyComp R X Y X (zero_add 0) u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y (zero_add 0) v u = dgHomologyId R Y) (d : ℤ)
    (a : (dgHomComplex R Z Y).homology d) :
    (homotopyPostcompEquiv R Z u v huv hvu d).symm a =
      dgHomologyComp R Z Y X (add_zero d) a v :=
  (rfl)

private def homotopyPrecompEquiv (Z : C) {X Y : C}
    (u : (dgHomComplex R X Y).homology 0) (v : (dgHomComplex R Y X).homology 0)
    (huv : dgHomologyComp R X Y X (zero_add 0) u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y (zero_add 0) v u = dgHomologyId R Y) (d : ℤ) :
    (dgHomComplex R X Z).homology d ≃ₗ[R] (dgHomComplex R Y Z).homology d where
  toFun := dgHomologyComp R Y X Z (zero_add d) v
  invFun := dgHomologyComp R X Y Z (zero_add d) u
  left_inv b := by
    rw [← dgHomologyComp_assoc R (zero_add 0) (zero_add d) (zero_add d) (zero_add d),
      huv, dgHomologyId_dgHomologyComp]
  right_inv b := by
    rw [← dgHomologyComp_assoc R (zero_add 0) (zero_add d) (zero_add d) (zero_add d),
      hvu, dgHomologyId_dgHomologyComp]
  map_add' := map_add _
  map_smul' := map_smul _

private theorem homotopyPrecompEquiv_symm_apply (Z : C) {X Y : C}
    (u : (dgHomComplex R X Y).homology 0) (v : (dgHomComplex R Y X).homology 0)
    (huv : dgHomologyComp R X Y X (zero_add 0) u v = dgHomologyId R X)
    (hvu : dgHomologyComp R Y X Y (zero_add 0) v u = dgHomologyId R Y) (d : ℤ)
    (b : (dgHomComplex R Y Z).homology d) :
    (homotopyPrecompEquiv R Z u v huv hvu d).symm b =
      dgHomologyComp R X Y Z (zero_add d) u b :=
  (rfl)

/-- Two objects `X` and `Y` of an `R`-linear DG category have **finite total graded `Hom`**
(Seidel–Thomas condition (K2)) when each cohomology module `(dgHomComplex R X Y).homology d` is
finitely generated and only finitely many degrees `d : ℤ` are nontrivial. -/
structure HasFiniteTotalGradedHom (X Y : C) : Prop where
  /-- Each graded cohomology group is finitely generated over `R`. -/
  finite (d : ℤ) : Module.Finite R ((dgHomComplex R X Y).homology d)
  /-- Only finitely many cohomological degrees are nontrivial. -/
  bdd_support : {d : ℤ | Nontrivial ((dgHomComplex R X Y).homology d)}.Finite

/-- An explicit finite superset of nontrivial cohomology degrees together with degreewise
finiteness yields `HasFiniteTotalGradedHom`. -/
theorem HasFiniteTotalGradedHom.of_finset {X Y : C} (s : Finset ℤ)
    [∀ d : ℤ, Module.Finite R ((dgHomComplex R X Y).homology d)]
    (hs : ∀ d ∉ s, Subsingleton ((dgHomComplex R X Y).homology d)) :
    HasFiniteTotalGradedHom R X Y where
  finite _ := inferInstance
  bdd_support := s.finite_toSet.subset fun d hd ↦ by
    by_contra hns
    exact @false_of_nontrivial_of_subsingleton _ hd (hs d hns)

variable {R} in
/-- Transport `HasFiniteTotalGradedHom` along degreewise linear equivalences reindexed by an
equivalence `σ : ℤ ≃ ℤ`. -/
theorem HasFiniteTotalGradedHom.of_equiv {C' : Type u'} [DGCategory R C']
    {X Y : C} {X' Y' : C'} (h : HasFiniteTotalGradedHom R X Y) (σ : ℤ ≃ ℤ)
    (e : ∀ d : ℤ, (dgHomComplex R X Y).homology (σ d) ≃ₗ[R]
      (dgHomComplex R X' Y').homology d) :
    HasFiniteTotalGradedHom R X' Y' where
  finite d :=
    have := h.finite (σ d)
    Module.Finite.equiv (e d)
  bdd_support := by
    refine (h.bdd_support.preimage σ.injective.injOn).subset fun d hd ↦ ?_
    let _ : Nontrivial ((dgHomComplex R X' Y').homology d) := hd
    exact (e d).toEquiv.nontrivial

variable {R} in
/-- Transport `HasFiniteTotalGradedHom` along degree-preserving linear equivalences. -/
theorem HasFiniteTotalGradedHom.of_linearEquiv {C' : Type u'} [DGCategory R C']
    {X Y : C} {X' Y' : C'} (h : HasFiniteTotalGradedHom R X Y)
    (e : ∀ d : ℤ, (dgHomComplex R X Y).homology d ≃ₗ[R]
      (dgHomComplex R X' Y').homology d) :
    HasFiniteTotalGradedHom R X' Y' :=
  h.of_equiv (Equiv.refl ℤ) e

/-- Infinitely many nontrivial cohomology degrees preclude `HasFiniteTotalGradedHom`, even if each
individual degree is finitely generated. -/
theorem not_hasFiniteTotalGradedHom_of_infinite {X Y : C}
    (h : {d : ℤ | Nontrivial ((dgHomComplex R X Y).homology d)}.Infinite) :
    ¬ HasFiniteTotalGradedHom R X Y :=
  fun hfin ↦ h hfin.bdd_support

/-- Seidel–Thomas's (K2) check: an object pair with nontrivial cohomology in every non-negative
even degree `2 * i` (`i : ℕ`) does not have finite total graded `Hom`. -/
theorem not_hasFiniteTotalGradedHom_of_nontrivial_two_mul {X Y : C}
    (h : ∀ i : ℕ, Nontrivial ((dgHomComplex R X Y).homology (2 * (i : ℤ)))) :
    ¬ HasFiniteTotalGradedHom R X Y :=
  not_hasFiniteTotalGradedHom_of_infinite R <|
    Set.infinite_of_injective_forall_mem (f := fun i : ℕ ↦ (2 * (i : ℤ)))
      (fun a b (hab : 2 * (a : ℤ) = 2 * (b : ℤ)) ↦ by omega) h

/-- The total graded `Hom` rank `∑ᶠ d : ℤ, Module.finrank R Hom^d(X, Y)`. -/
def dgTotalHomFinrank (X Y : C) : ℕ :=
  ∑ᶠ d : ℤ, Module.finrank R ((dgHomComplex R X Y).homology d)

/-- The graded Euler pairing `χ(X, Y) = ∑ᶠ d : ℤ, (-1)^d * Module.finrank R Hom^d(X, Y)`. -/
def dgEulerPairing (X Y : C) : ℤ :=
  ∑ᶠ d : ℤ, (d.negOnePow : ℤ) * (Module.finrank R ((dgHomComplex R X Y).homology d) : ℤ)

section NontrivialRing

variable [Nontrivial R]

/-- When cohomology vanishes outside a finite set `s : Finset ℤ`, `dgTotalHomFinrank` equals the
finite sum over `s`. -/
theorem dgTotalHomFinrank_eq_sum {X Y : C} (s : Finset ℤ)
    (hs : ∀ d ∉ s, Subsingleton ((dgHomComplex R X Y).homology d)) :
    dgTotalHomFinrank R X Y =
      ∑ d ∈ s, Module.finrank R ((dgHomComplex R X Y).homology d) := by
  refine finsum_eq_sum_of_support_subset _ fun d hd ↦ ?_
  by_contra hns
  have := hs d hns
  exact hd Module.finrank_zero_of_subsingleton

/-- When cohomology vanishes outside a finite set `s : Finset ℤ`, `dgEulerPairing` equals the
alternating finite sum over `s`. -/
theorem dgEulerPairing_eq_sum {X Y : C} (s : Finset ℤ)
    (hs : ∀ d ∉ s, Subsingleton ((dgHomComplex R X Y).homology d)) :
    dgEulerPairing R X Y =
      ∑ d ∈ s, (d.negOnePow : ℤ) * (Module.finrank R ((dgHomComplex R X Y).homology d) : ℤ) := by
  refine finsum_eq_sum_of_support_subset _ fun d hd ↦ ?_
  by_contra hns
  have := hs d hns
  apply hd
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

end NontrivialRing

end CommRing

/-! ### Spherical objects over a field -/

section Field

variable (k : Type v) [Field k] {C : Type u} [DGCategory k C]

/-- An object `E` of a `k`-linear DG category is **`n`-spherical** (Seidel–Thomas, Definition 2.9)
if `0 < n`, `E` has finite total graded `Hom` to every object (K2), `Hom^*(E, E)` is
one-dimensional in degrees `0` and `n` and vanishes in all other degrees (K3), and `Hom^n(E, E)`
admits a linear trace making graded composition `Hom^d(E, F) × Hom^{n - d}(F, E) → k` a perfect
pairing for every object `F` and degree `d : ℤ` (K4). -/
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
      ∀ (F : C) (d : ℤ),
        ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr).IsPerfPair

/-- Seidel–Thomas's `n > 0` check: no object is `n`-spherical for `n ≤ 0` (in particular
`n = 0`). -/
theorem not_isSphericalObject_of_nonpos {n : ℤ} (hn : n ≤ 0) (E : C) :
    ¬ IsSphericalObject k n E :=
  fun hE ↦ (not_lt_of_ge hn) hE.pos

/-- An object violating finite total self-`Hom` (for example with `Hom^{2i}(E, E) ≠ 0` for all
`i : ℕ`) cannot be `n`-spherical. -/
theorem not_isSphericalObject_of_nontrivial_two_mul (n : ℤ) {E : C}
    (h : ∀ i : ℕ, Nontrivial ((dgHomComplex k E E).homology (2 * (i : ℤ)))) :
    ¬ IsSphericalObject k n E :=
  fun hE ↦ not_hasFiniteTotalGradedHom_of_nontrivial_two_mul k h (hE.hasFiniteTotalGradedHom_from E)

namespace IsSphericalObject

variable {k} {n : ℤ} {E : C}

/-- Every `n`-spherical object has nonzero cohomology identity class `dgHomologyId k E`. -/
theorem dgHomologyId_ne_zero (hE : IsSphericalObject k n E) :
    dgHomologyId k E ≠ 0 := by
  have hnt : Nontrivial ((dgHomComplex k E E).homology 0) :=
    Module.nontrivial_of_finrank_pos (by rw [hE.finrank_homology_zero]; exact Nat.one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : (dgHomComplex k E E).homology 0)
  intro hid
  apply hx
  rw [← dgHomologyId_dgHomologyComp k x, hid, map_zero, LinearMap.zero_apply]

/-- Degree-zero cohomology endomorphisms of an `n`-spherical object are spanned by
`dgHomologyId k E`. -/
theorem span_dgHomologyId_eq_top (hE : IsSphericalObject k n E) :
    Submodule.span k {dgHomologyId k E} = ⊤ := by
  have := (hE.hasFiniteTotalGradedHom_from E).finite 0
  exact Submodule.eq_top_of_finrank_eq <|
    (finrank_span_singleton hE.dgHomologyId_ne_zero).trans hE.finrank_homology_zero.symm

/-- Serre duality (K4) gives a linear equivalence `Hom^{n - d}(F, E) ≃ₗ[k] Dual(Hom^d(E, F))`, so
finite total graded `Hom` out of `E` implies finite total graded `Hom` into `E`. -/
theorem hasFiniteTotalGradedHom_to (hE : IsSphericalObject k n E) (F : C) :
    HasFiniteTotalGradedHom k F E := by
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  have hfrom := hE.hasFiniteTotalGradedHom_from F
  refine ⟨fun d ↦ ?_, ?_⟩
  · have := htr F (n - d)
    have _ : Module.Finite k ((dgHomComplex k E F).homology (n - d)) := hfrom.finite (n - d)
    let p := ((dgHomologyComp k E F E (add_sub_cancel (n - d) n)).compr₂ tr).flip
    have _ : Module.Finite k ((dgHomComplex k F E).homology (n - (n - d))) :=
      Module.Finite.equiv p.toPerfPair.symm
    exact Module.Finite.equiv (homologyCastEquiv k F E (by omega : n - (n - d) = d))
  · refine ((hfrom.bdd_support.image (fun d ↦ n - d)).subset fun d hd ↦ ?_)
    refine ⟨n - d, ?_, by dsimp only; omega⟩
    have := htr F (n - d)
    let _ : Nontrivial ((dgHomComplex k F E).homology d) := hd
    let p := ((dgHomologyComp k E F E (add_sub_cancel (n - d) n)).compr₂ tr).flip
    have _ : Nontrivial ((dgHomComplex k F E).homology (n - (n - d))) :=
      (homologyCastEquiv k F E (by omega : n - (n - d) = d)).toEquiv.nontrivial
    have hdual : Nontrivial (Module.Dual k ((dgHomComplex k E F).homology (n - d))) :=
      p.toPerfPair.symm.toEquiv.nontrivial
    by_contra hsub
    rw [Set.mem_ofPred_eq, not_nontrivial_iff_subsingleton] at hsub
    exact @false_of_nontrivial_of_subsingleton _ hdual inferInstance

/-- Complementary cohomology groups `Hom^d(E, F)` and `Hom^{n - d}(F, E)` of an `n`-spherical
object `E` have equal `finrank`. -/
theorem finrank_homology_symm (hE : IsSphericalObject k n E) (F : C) (d : ℤ) :
    Module.finrank k ((dgHomComplex k F E).homology (n - d)) =
      Module.finrank k ((dgHomComplex k E F).homology d) := by
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  have := htr F d
  let p := ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr).flip
  exact p.toPerfPair.finrank_eq.trans Subspace.dual_finrank_eq

/-- Total graded `Hom` dimensions into and out of an `n`-spherical object coincide:
`dgTotalHomFinrank k F E = dgTotalHomFinrank k E F`. -/
theorem dgTotalHomFinrank_symm (hE : IsSphericalObject k n E) (F : C) :
    dgTotalHomFinrank k F E = dgTotalHomFinrank k E F := by
  rw [dgTotalHomFinrank, dgTotalHomFinrank,
    ← finsum_comp_equiv (Equiv.subLeft n)
      (f := fun d ↦ Module.finrank k ((dgHomComplex k F E).homology d))]
  exact finsum_congr fun d ↦ hE.finrank_homology_symm F d

/-- Every witnessing trace functional of an `n`-spherical object is nonzero. -/
theorem trace_ne_zero (hE : IsSphericalObject k n E)
    {tr : (dgHomComplex k E E).homology n →ₗ[k] k}
    (htr : ∀ (F : C) (d : ℤ),
      ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr).IsPerfPair) :
    tr ≠ 0 := by
  have hnt : Nontrivial ((dgHomComplex k E E).homology n) :=
    Module.nontrivial_of_finrank_pos (by rw [hE.finrank_homology_top]; exact Nat.one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : (dgHomComplex k E E).homology n)
  intro hzero
  have := htr E n
  apply hx
  apply (LinearMap.IsPerfPair.bijective_left
    ((dgHomologyComp k E E E (add_sub_cancel n n)).compr₂ tr)).injective
  rw [map_zero, hzero]
  apply LinearMap.ext fun _ ↦ rfl

/-- Because `Hom^n(E, E)` is one-dimensional, **every** nonzero functional
`tr' : Hom^n(E, E) →ₗ[k] k` makes composition a perfect pairing for an `n`-spherical object `E`. -/
theorem isPerfPair_of_trace_ne_zero (hE : IsSphericalObject k n E)
    {tr' : (dgHomComplex k E E).homology n →ₗ[k] k} (htr' : tr' ≠ 0) (F : C) (d : ℤ) :
    ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr').IsPerfPair := by
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  have htr0 : tr ≠ 0 := hE.trace_ne_zero htr
  have hfd : Module.finrank k (Module.Dual k ((dgHomComplex k E E).homology n)) = 1 :=
    Subspace.dual_finrank_eq.trans hE.finrank_homology_top
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' tr htr0).mp hfd tr'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact htr' (by rw [← hc, zero_smul])
  have _ := htr F d
  have heq : (dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr' =
      c • ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr) := by
    apply LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
    simp only [LinearMap.compr₂_apply, ← hc, LinearMap.smul_apply]
  rw [heq]
  exact LinearMap.IsPerfPair.smul_of_isUnit hc0.isUnit _

/-- An `n`-spherical object has total graded endomorphism dimension `2`. -/
theorem dgTotalHomFinrank_self (hE : IsSphericalObject k n E) :
    dgTotalHomFinrank k E E = 2 := by
  have hne : (0 : ℤ) ≠ n := ne_of_lt hE.pos
  rw [dgTotalHomFinrank_eq_sum k ({0, n} : Finset ℤ) fun d hd ↦ by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    exact hE.subsingleton_homology_of_ne hd.1 hd.2]
  rw [Finset.sum_pair hne, hE.finrank_homology_zero, hE.finrank_homology_top]

/-- The self-Euler pairing of an `n`-spherical object is `1 + (-1)^n` (hence `2` for even `n` and
`0` for odd `n`). -/
theorem dgEulerPairing_self (hE : IsSphericalObject k n E) :
    dgEulerPairing k E E = 1 + (n.negOnePow : ℤ) := by
  have hne : (0 : ℤ) ≠ n := ne_of_lt hE.pos
  rw [dgEulerPairing_eq_sum k ({0, n} : Finset ℤ) fun d hd ↦ by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    exact hE.subsingleton_homology_of_ne hd.1 hd.2]
  rw [Finset.sum_pair hne, hE.finrank_homology_zero, hE.finrank_homology_top]
  simp only [Int.negOnePow_zero, Units.val_one, Nat.cast_one, mul_one]

/-- Every even-dimensional spherical object has self-Euler pairing `2`. -/
theorem dgEulerPairing_self_of_even (hE : IsSphericalObject k n E) (hn : Even n) :
    dgEulerPairing k E E = 2 := by
  rw [hE.dgEulerPairing_self, Int.negOnePow_even _ hn, Units.val_one]
  norm_num

/-! ### Invariance under shifted cohomology equivalences, quasi-equivalences, and shifts -/

/-- A mutually inverse pair of cohomology classes `u ∈ Hom^{-m}(E, E')` and `v ∈ Hom^m(E', E)`
transports `n`-sphericality from `E` to `E'`. -/
theorem of_gradedEquiv {E' : C} (hE : IsSphericalObject k n E) {m : ℤ}
    (u : (dgHomComplex k E E').homology (-m)) (v : (dgHomComplex k E' E).homology m)
    (huv : dgHomologyComp k E E' E (neg_add_cancel m) u v = dgHomologyId k E)
    (hvu : dgHomologyComp k E' E E' (add_neg_cancel m) v u = dgHomologyId k E') :
    IsSphericalObject k n E' := by
  let eLeft (F : C) (d : ℤ) :
      (dgHomComplex k E F).homology (d - m) ≃ₗ[k] (dgHomComplex k E' F).homology d :=
    { toFun := dgHomologyComp k E' E F (by omega) v
      invFun := dgHomologyComp k E E' F (by omega) u
      left_inv a := by
        rw [← dgHomologyComp_assoc k (neg_add_cancel m) (by omega) (by omega) (by omega), huv,
          dgHomologyId_dgHomologyComp]
      right_inv a := by
        rw [← dgHomologyComp_assoc k (add_neg_cancel m) (by omega) (by omega) (by omega), hvu,
          dgHomologyId_dgHomologyComp]
      map_add' := map_add _
      map_smul' := map_smul _ }
  let eRight (F : C) (d : ℤ) :
      (dgHomComplex k F E).homology (d + m) ≃ₗ[k] (dgHomComplex k F E').homology d :=
    { toFun := (dgHomologyComp k F E E' (by omega)).flip u
      invFun := (dgHomologyComp k F E' E (by omega)).flip v
      left_inv a := by
        dsimp only [LinearMap.flip_apply]
        rw [dgHomologyComp_assoc k (by omega) (neg_add_cancel m) (by omega) (by omega), huv,
          dgHomologyComp_dgHomologyId]
      right_inv a := by
        dsimp only [LinearMap.flip_apply]
        rw [dgHomologyComp_assoc k (by omega) (add_neg_cancel m) (by omega) (by omega), hvu,
          dgHomologyComp_dgHomologyId]
      map_add' := map_add _
      map_smul' := map_smul _ }
  let eEnd (d : ℤ) :
      (dgHomComplex k E E).homology d ≃ₗ[k] (dgHomComplex k E' E').homology d :=
    (homologyCastEquiv k E E (by omega : d = (d - m) + m)).trans
      ((eRight E (d - m)).trans (eLeft E' d))
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  refine
    { pos := hE.pos
      hasFiniteTotalGradedHom_from := fun F ↦
        (hE.hasFiniteTotalGradedHom_from F).of_equiv (Equiv.subRight m) (eLeft F)
      finrank_homology_zero := (eEnd 0).symm.finrank_eq.trans hE.finrank_homology_zero
      finrank_homology_top := (eEnd n).symm.finrank_eq.trans hE.finrank_homology_top
      subsingleton_homology_of_ne := fun hd0 hdn ↦
        have := hE.subsingleton_homology_of_ne hd0 hdn
        (eEnd _).toEquiv.subsingleton_congr.mp inferInstance
      exists_trace_isPerfPair := ⟨tr.comp (eEnd n).symm.toLinearMap, fun F d ↦ ?_⟩ }
  have _ := htr F (d - m)
  have heq : (dgHomologyComp k E' F E' (add_sub_cancel d n)).compr₂
        (tr.comp (eEnd n).symm.toLinearMap) =
      ((dgHomologyComp k E F E (add_sub_cancel (d - m) n)).compr₂ tr).compl₁₂
        (eLeft F d).symm.toLinearMap
        ((eRight F (n - d)).symm.trans
          (homologyCastEquiv k F E (by omega : n - d + m = n - (d - m)))).toLinearMap := by
    apply LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₁₂_apply,
      LinearEquiv.coe_coe, eEnd, eLeft, eRight, LinearEquiv.symm_trans_apply,
      LinearEquiv.trans_apply, LinearEquiv.coe_symm_mk, LinearMap.flip_apply]
    apply congrArg tr
    have hassoc :
        dgHomologyComp k E E' E (rfl : (n - m) + m = (n - m) + m)
          (dgHomologyComp k E E' E' (by omega : -m + n = n - m) u
            (dgHomologyComp k E' F E' (add_sub_cancel d n) a b)) v =
        dgHomologyComp k E F E (by omega : (d - m) + (n - d + m) = (n - m) + m)
          (dgHomologyComp k E E' F (by omega : -m + d = d - m) u a)
          (dgHomologyComp k F E' E (rfl : n - d + m = n - d + m) b v) := by
      rw [← dgHomologyComp_assoc k (pq := d - m) (by omega) (add_sub_cancel d n)
          (by omega) (by omega) u a b,
        dgHomologyComp_assoc k (qr := n - d + m) (by omega) (rfl : n - d + m = n - d + m)
          (rfl : (n - m) + m = (n - m) + m) (by omega) _ b v]
    rw [hassoc]
    obtain ⟨f, hf, hfa⟩ :=
      exists_dgHomologyClass_eq k (dgHomologyComp k E E' F (by omega : -m + d = d - m) u a)
    obtain ⟨g, hg, hgb⟩ :=
      exists_dgHomologyClass_eq k (dgHomologyComp k F E' E (rfl : n - d + m = n - d + m) b v)
    rw [← hfa, ← hgb, homologyCastEquiv_symm,
      homologyCastEquiv_dgHomologyClass k (by omega : n - d + m = n - (d - m)) g hg,
      dgHomologyComp_dgHomologyClass, dgHomologyComp_dgHomologyClass,
      homologyCastEquiv_dgHomologyClass k (by omega : (n - m) + m = n)]
    exact dgHomologyClass_congr k _ _
      ((dgComp_castDeg k (by omega : n - d + m = n - (d - m))
        (by omega : (n - m) + m = n) f g (add_sub_cancel (d - m) n)).symm)
  rw [heq]
  infer_instance

/-- Isomorphic objects in `DGHomotopyCategory k C` have equivalent `n`-sphericality. -/
theorem of_homotopyIso {E' : C} (hE : IsSphericalObject k n E)
    (e : DGHomotopyCategory.of k E ≅ DGHomotopyCategory.of k E') :
    IsSphericalObject k n E' := by
  obtain ⟨u, v, huv, hvu⟩ := homotopyIso_exists_classes k e
  exact hE.of_gradedEquiv (m := 0) u v huv hvu

end IsSphericalObject

/-! ### `A_m`-configurations of spherical objects -/

/-- A sequence `E : Fin m → C` is an **`A_m`-configuration of `n`-spherical objects**
(Seidel–Thomas, Definition 2.15) if each `E i` is `n`-spherical and, for distinct `i ≠ j`, the
total graded `Hom` space between `E i` and `E j` has dimension `1` when `|i - j| = 1` and `0`
otherwise. -/
structure IsAmSphericalConfiguration (m : ℕ) (n : ℤ) (E : Fin m → C) : Prop where
  /-- Every object in the configuration is `n`-spherical. -/
  isSphericalObject (i : Fin m) : IsSphericalObject k n (E i)
  /-- Adjacent objects in the `A_m` chain have one-dimensional total graded `Hom`. -/
  dgTotalHomFinrank_of_adj {i j : Fin m}
    (hadj : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) :
    dgTotalHomFinrank k (E i) (E j) = 1
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
  refine ⟨fun hPm ↦ ?_, fun hP ↦ hP.of_gradedEquiv u v huv hvu⟩
  let v' := homologyCastEquiv k ((shiftFunctor k m).obj P) P (neg_neg m).symm v
  have hv' : v' = dgHomologyClass k (castDeg k (neg_neg m).symm (fromShift P m))
      (dgDifferential_castDeg_eq_zero k (neg_neg m).symm (dgDifferential_fromShift P m)) :=
    homologyCastEquiv_dgHomologyClass k (neg_neg m).symm (fromShift P m)
      (dgDifferential_fromShift P m)
  refine hPm.of_gradedEquiv v' u ?_ ?_
  · rw [hv', dgHomologyComp_dgHomologyClass, dgHomologyId_def]
    refine dgHomologyClass_congr k _ _ ?_
    rw [castDeg_dgComp k (neg_neg m).symm rfl, castDeg_self, dgComp_fromShift_toShift]
  · rw [hv', dgHomologyComp_dgHomologyClass, dgHomologyId_def]
    refine dgHomologyClass_congr k _ _ ?_
    rw [dgComp_castDeg k (neg_neg m).symm rfl, castDeg_self, dgComp_toShift_fromShift]

end DGTwistedObject

end TauCeti

namespace CategoryTheory.EnrichedFunctor

open TauCeti HomologicalComplex

universe v u₁ u₂

section CommRing

variable {R : Type v} [CommRing R] {C : Type u₁} {D : Type u₂}
  [DGCategory R C] [DGCategory R D]
  {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D}

/-- A quasi-fully faithful DG functor induces linear equivalences on all Hom cohomology groups. -/
def IsQuasiFullyFaithful.homologyLinearEquiv (hF : F.IsQuasiFullyFaithful)
    (X Y : C) (d : ℤ) :
    (dgHomComplex R X Y).homology d ≃ₗ[R] (dgHomComplex R (F.obj X) (F.obj Y)).homology d :=
  have := hF.isIso_homologyMap X Y d
  (asIso (homologyMap (F.map X Y) d)).toLinearEquiv

/-- `IsQuasiFullyFaithful.homologyLinearEquiv` acts via `HomologicalComplex.homologyMap`. -/
@[simp]
theorem IsQuasiFullyFaithful.homologyLinearEquiv_apply (hF : F.IsQuasiFullyFaithful)
    (X Y : C) (d : ℤ) (x : (dgHomComplex R X Y).homology d) :
    hF.homologyLinearEquiv X Y d x = (homologyMap (F.map X Y) d).hom x :=
  (rfl)

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

variable {k : Type v} [Field k] {C : Type u₁} {D : Type u₂}
  [DGCategory k C] [DGCategory k D]
  {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} k) ℤ) C D}

/-- A DG quasi-equivalence preserves and reflects `n`-spherical objects. -/
theorem IsQuasiEquivalence.isSphericalObject_iff (hF : F.IsQuasiEquivalence)
    (n : ℤ) (E : C) :
    IsSphericalObject k n (F.obj E) ↔ IsSphericalObject k n E := by
  have hff := hF.isQuasiFullyFaithful
  constructor
  · intro hFE
    obtain ⟨tr, htr⟩ := hFE.exists_trace_isPerfPair
    refine
      { pos := hFE.pos
        hasFiniteTotalGradedHom_from := fun X ↦
          (hFE.hasFiniteTotalGradedHom_from (F.obj X)).of_linearEquiv
            fun d ↦ (hff.homologyLinearEquiv E X d).symm
        finrank_homology_zero :=
          (hff.homologyLinearEquiv E E 0).finrank_eq.trans hFE.finrank_homology_zero
        finrank_homology_top :=
          (hff.homologyLinearEquiv E E n).finrank_eq.trans hFE.finrank_homology_top
        subsingleton_homology_of_ne := fun hd0 hdn ↦
          have := hFE.subsingleton_homology_of_ne hd0 hdn
          (hff.homologyLinearEquiv E E _).toEquiv.subsingleton_congr.mpr inferInstance
        exists_trace_isPerfPair :=
          ⟨tr.comp (hff.homologyLinearEquiv E E n).toLinearMap, fun X d ↦ ?_⟩ }
    have _ := htr (F.obj X) d
    have heq : (dgHomologyComp k E X E (add_sub_cancel d n)).compr₂
          (tr.comp (hff.homologyLinearEquiv E E n).toLinearMap) =
        ((dgHomologyComp k (F.obj E) (F.obj X) (F.obj E) (add_sub_cancel d n)).compr₂ tr).compl₁₂
          (hff.homologyLinearEquiv E X d).toLinearMap
          (hff.homologyLinearEquiv X E (n - d)).toLinearMap := by
      apply LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₁₂_apply,
        LinearEquiv.coe_coe, hff.homologyLinearEquiv_dgHomologyComp]
    rw [heq]
    infer_instance
  · intro hE
    obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
    refine
      { pos := hE.pos
        hasFiniteTotalGradedHom_from := fun Y ↦ by
          obtain ⟨X, ⟨eY⟩⟩ := hF.essentiallySurjective Y
          obtain ⟨u, v, huv, hvu⟩ := TauCeti.homotopyIso_exists_classes k eY
          exact ((hE.hasFiniteTotalGradedHom_from X).of_linearEquiv
            (hff.homologyLinearEquiv E X)).of_linearEquiv
            (TauCeti.homotopyPostcompEquiv k (F.obj E) u v huv hvu)
        finrank_homology_zero :=
          (hff.homologyLinearEquiv E E 0).symm.finrank_eq.trans hE.finrank_homology_zero
        finrank_homology_top :=
          (hff.homologyLinearEquiv E E n).symm.finrank_eq.trans hE.finrank_homology_top
        subsingleton_homology_of_ne := fun hd0 hdn ↦
          have := hE.subsingleton_homology_of_ne hd0 hdn
          (hff.homologyLinearEquiv E E _).toEquiv.subsingleton_congr.mp inferInstance
        exists_trace_isPerfPair :=
          ⟨tr.comp (hff.homologyLinearEquiv E E n).symm.toLinearMap, fun Y d ↦ ?_⟩ }
    obtain ⟨X, ⟨eY⟩⟩ := hF.essentiallySurjective Y
    obtain ⟨u, v, huv, hvu⟩ := TauCeti.homotopyIso_exists_classes k eY
    let eL := (TauCeti.homotopyPostcompEquiv k (F.obj E) u v huv hvu d).symm.trans
      (hff.homologyLinearEquiv E X d).symm
    let eR := (TauCeti.homotopyPrecompEquiv k (F.obj E) u v huv hvu (n - d)).symm.trans
      (hff.homologyLinearEquiv X E (n - d)).symm
    have _ := htr X d
    have heq : (dgHomologyComp k (F.obj E) Y (F.obj E) (add_sub_cancel d n)).compr₂
          (tr.comp (hff.homologyLinearEquiv E E n).symm.toLinearMap) =
        ((dgHomologyComp k E X E (add_sub_cancel d n)).compr₂ tr).compl₁₂
          eL.toLinearMap eR.toLinearMap := by
      apply LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.compl₁₂_apply,
        LinearEquiv.coe_coe]
      apply congrArg tr
      apply (hff.homologyLinearEquiv E E n).injective
      rw [LinearEquiv.apply_symm_apply, hff.homologyLinearEquiv_dgHomologyComp]
      simp only [eL, eR, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        TauCeti.homotopyPostcompEquiv_symm_apply, TauCeti.homotopyPrecompEquiv_symm_apply]
      rw [dgHomologyComp_assoc k (add_zero d) (zero_add (n - d)) (add_sub_cancel d n)
          (add_sub_cancel d n),
        ← dgHomologyComp_assoc k (zero_add 0) (zero_add (n - d)) (zero_add (n - d))
          (zero_add (n - d)),
        hvu, dgHomologyId_dgHomologyComp]
    rw [heq]
    infer_instance

end Field

end CategoryTheory.EnrichedFunctor

