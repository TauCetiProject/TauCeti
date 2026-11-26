/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.CategoryTheory.DG.QuasiEquivalence
public import TauCeti.CategoryTheory.DG.Twisted.Shift
public import TauCeti.LinearAlgebra.PerfectPairing.Basic

/-!
# Spherical objects and `A_m`-configurations in differential graded categories

Following Seidel and Thomas (*Braid group actions on derived categories of coherent sheaves*,
Definitions 2.5, 2.9, and 2.15), we formalize `TauCeti.HasFiniteTotalGradedHom` (K2),
`TauCeti.dgTotalHomFinrank`, `TauCeti.dgEulerPairing`, `n`-spherical objects
`TauCeti.IsSphericalObject` (K3–K4, `0 < n`), their transport and reflection across shifted
cohomology equivalences, `H⁰`-isomorphisms, quasi-fully faithful DG functors, DG quasi-equivalences,
and twisted shifts, and `A_m`-configurations `TauCeti.IsAmSphericalConfiguration`.

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
    HasFiniteTotalGradedHom R X Y :=
  ⟨fun _ ↦ inferInstance, s.finite_toSet.subset fun d hd ↦ by
    by_contra hns; exact @false_of_nontrivial_of_subsingleton _ hd (hs d hns)⟩

variable {R} in
/-- Transport `HasFiniteTotalGradedHom` along degreewise linear equivalences reindexed by `σ`. -/
theorem HasFiniteTotalGradedHom.of_equiv {C' : Type u'} [DGCategory R C']
    {X Y : C} {X' Y' : C'} (h : HasFiniteTotalGradedHom R X Y) (σ : ℤ ≃ ℤ)
    (e : ∀ d : ℤ, (dgHomComplex R X Y).homology (σ d) ≃ₗ[R] (dgHomComplex R X' Y').homology d) :
    HasFiniteTotalGradedHom R X' Y' :=
  ⟨fun d ↦ by have := h.finite (σ d); exact Module.Finite.equiv (e d),
   (h.bdd_support.preimage σ.injective.injOn).subset fun d hd ↦
     @Equiv.nontrivial _ _ (e d).toEquiv hd⟩

variable {R} in
/-- Transport `HasFiniteTotalGradedHom` along degree-preserving linear equivalences. -/
theorem HasFiniteTotalGradedHom.of_linearEquiv {C' : Type u'} [DGCategory R C']
    {X Y : C} {X' Y' : C'} (h : HasFiniteTotalGradedHom R X Y)
    (e : ∀ d : ℤ, (dgHomComplex R X Y).homology d ≃ₗ[R] (dgHomComplex R X' Y').homology d) :
    HasFiniteTotalGradedHom R X' Y' := h.of_equiv (Equiv.refl ℤ) e

/-- Infinitely many nontrivial cohomology degrees preclude `HasFiniteTotalGradedHom`. -/
theorem not_hasFiniteTotalGradedHom_of_infinite {X Y : C}
    (h : {d : ℤ | Nontrivial ((dgHomComplex R X Y).homology d)}.Infinite) :
    ¬ HasFiniteTotalGradedHom R X Y := fun hfin ↦ h hfin.bdd_support

/-- The total graded `Hom` rank `∑ᶠ d : ℤ, Module.finrank R Hom^d(X, Y)`. -/
def dgTotalHomFinrank (X Y : C) : ℕ := ∑ᶠ d : ℤ, Module.finrank R ((dgHomComplex R X Y).homology d)

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

/-- An object with infinitely many nontrivial self-cohomology degrees cannot be `n`-spherical. -/
theorem not_isSphericalObject_of_infinite (n : ℤ) {E : C}
    (h : {d : ℤ | Nontrivial ((dgHomComplex k E E).homology d)}.Infinite) :
    ¬ IsSphericalObject k n E :=
  fun hE ↦ not_hasFiniteTotalGradedHom_of_infinite k h (hE.hasFiniteTotalGradedHom_from E)

namespace IsSphericalObject

variable {k} {n : ℤ} {E : C}

/-- Every `n`-spherical object has nonzero cohomology identity class `dgHomologyId k E`. -/
theorem dgHomologyId_ne_zero (hE : IsSphericalObject k n E) : dgHomologyId k E ≠ 0 := by
  have := Module.nontrivial_of_finrank_pos (by rw [hE.finrank_homology_zero]; exact Nat.one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : (dgHomComplex k E E).homology 0)
  intro hid; apply hx; rw [← dgHomologyId_dgHomologyComp k x, hid, map_zero, LinearMap.zero_apply]

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
    (dgHomologyCastEquiv k F E (sub_sub_self n d))

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
theorem trace_ne_zero (hE : IsSphericalObject k n E) {tr : (dgHomComplex k E E).homology n →ₗ[k] k}
    (htr : ∀ (F : C) (d : ℤ),
      ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr).IsPerfPair) : tr ≠ 0 := by
  have := Module.nontrivial_of_finrank_pos (by rw [hE.finrank_homology_top]; exact Nat.one_pos)
  obtain ⟨x, hx⟩ := exists_ne (0 : (dgHomComplex k E E).homology n); rintro rfl; have := htr E n
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
  have := htr F d; convert LinearMap.IsPerfPair.smul_of_isUnit hc0.isUnit
    ((dgHomologyComp k E F E (add_sub_cancel d n)).compr₂ tr)
  ext a b; simp [← hc]

private theorem subsingleton_not_mem_pair (hE : IsSphericalObject k n E) {d : ℤ}
    (hd : d ∉ ({0, n} : Finset ℤ)) : Subsingleton ((dgHomComplex k E E).homology d) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  exact hE.subsingleton_homology_of_ne hd.left hd.right

/-- An `n`-spherical object has total graded endomorphism dimension `2`. -/
theorem dgTotalHomFinrank_self (hE : IsSphericalObject k n E) : dgTotalHomFinrank k E E = 2 := by
  rw [dgTotalHomFinrank_eq_sum k ({0, n} : Finset ℤ) fun _ ↦ hE.subsingleton_not_mem_pair,
    Finset.sum_pair (ne_of_lt hE.pos), hE.finrank_homology_zero, hE.finrank_homology_top]

/-- The self-Euler pairing of an `n`-spherical object is `1 + (-1)^n`. -/
theorem dgEulerPairing_self (hE : IsSphericalObject k n E) :
    dgEulerPairing k E E = 1 + (n.negOnePow : ℤ) := by
  rw [dgEulerPairing_eq_sum k ({0, n} : Finset ℤ) fun _ ↦ hE.subsingleton_not_mem_pair,
    Finset.sum_pair (ne_of_lt hE.pos), hE.finrank_homology_zero, hE.finrank_homology_top]; simp

/-- Every even-dimensional spherical object has self-Euler pairing `2`. -/
theorem dgEulerPairing_self_of_even (hE : IsSphericalObject k n E) (hn : Even n) :
    dgEulerPairing k E E = 2 := by
  rw [hE.dgEulerPairing_self, Int.negOnePow_even _ hn, Units.val_one]; norm_num

/-- Transport `n`-sphericality from `E : C` to `E' : C'` along endomorphism cohomology equivalences
`eEnd` and objectwise left/right cohomology equivalences `eLeft`, `eRight` indexed by `φ : C' → C`
and an injective degree map `σ : ℤ → ℤ` that intertwine `TauCeti.dgHomologyComp`. -/
theorem of_homologyEquiv {C' : Type u'} [DGCategory k C'] {E' : C'}
    (hE : IsSphericalObject k n E) (φ : C' → C) (σ : ℤ → ℤ) (hσ : Function.Injective σ)
    (eEnd : ∀ d : ℤ,
      (dgHomComplex k E' E').homology d ≃ₗ[k] (dgHomComplex k E E).homology d)
    (eLeft : ∀ (Y : C') (d : ℤ),
      (dgHomComplex k E' Y).homology d ≃ₗ[k] (dgHomComplex k E (φ Y)).homology (σ d))
    (eRight : ∀ (Y : C') (d : ℤ),
      (dgHomComplex k Y E').homology (n - d) ≃ₗ[k]
        (dgHomComplex k (φ Y) E).homology (n - σ d))
    (hcomp : ∀ (Y : C') (d : ℤ) (a : (dgHomComplex k E' Y).homology d)
      (b : (dgHomComplex k Y E').homology (n - d)),
      eEnd n (dgHomologyComp k E' Y E' (add_sub_cancel d n) a b) =
        dgHomologyComp k E (φ Y) E (add_sub_cancel (σ d) n)
          (eLeft Y d a) (eRight Y d b)) :
    IsSphericalObject k n E' := by
  obtain ⟨tr, htr⟩ := hE.exists_trace_isPerfPair
  refine ⟨hE.pos, fun Y ↦ ⟨fun d ↦ by
      have := (hE.hasFiniteTotalGradedHom_from (φ Y)).finite (σ d)
      exact Module.Finite.equiv (eLeft Y d).symm,
    ((hE.hasFiniteTotalGradedHom_from (φ Y)).bdd_support.preimage hσ.injOn).subset fun d hd ↦
      @Equiv.nontrivial _ _ (eLeft Y d).symm.toEquiv hd⟩,
    (eEnd 0).finrank_eq.trans hE.finrank_homology_zero,
    (eEnd n).finrank_eq.trans hE.finrank_homology_top, fun hd0 hdn ↦ by
      have := hE.subsingleton_homology_of_ne hd0 hdn
      exact (eEnd _).toEquiv.subsingleton_congr.mpr inferInstance,
    ⟨tr.comp (eEnd n).toLinearMap, fun Y d ↦ ?_⟩⟩
  have := htr (φ Y) (σ d)
  convert (inferInstance :
    (((dgHomologyComp k E (φ Y) E (add_sub_cancel (σ d) n)).compr₂ tr).compl₁₂
      (eLeft Y d).toLinearMap (eRight Y d).toLinearMap).IsPerfPair)
  ext a b; exact congrArg tr (hcomp Y d a b)

/-- A mutually inverse pair of cohomology classes `u ∈ Hom^p(E, E')` and `v ∈ Hom^q(E', E)` with
`p + q = 0` transports `n`-sphericality from `E` to `E'`. -/
theorem of_gradedEquiv {E' : C} (hE : IsSphericalObject k n E) {p q : ℤ} (hpq : p + q = 0)
    (u : (dgHomComplex k E E').homology p) (v : (dgHomComplex k E' E).homology q)
    (huv : dgHomologyComp k E E' E hpq u v = dgHomologyId k E)
    (hvu : dgHomologyComp k E' E E' ((add_comm q p).trans hpq) v u = dgHomologyId k E') :
    IsSphericalObject k n E' := by
  let eLeft (F : C) (d : ℤ) :=
    dgHomologyCompLeftEquiv k F hpq (rfl : p + d = p + d) u v huv hvu
  let eRight (F : C) (d : ℤ) :=
    (dgHomologyCompRightEquiv k F ((add_comm q p).trans hpq)
      (rfl : n - d + q = n - d + q) v u hvu huv).trans
      (dgHomologyCastEquiv k F E (by omega : n - d + q = n - (p + d)))
  let eEnd (d : ℤ) :=
    ((eLeft E' d).trans
      (dgHomologyCompRightEquiv k E ((add_comm q p).trans hpq)
        (rfl : p + d + q = p + d + q) v u hvu huv)).trans
      (dgHomologyCastEquiv k E E (by omega : p + d + q = d))
  refine hE.of_homologyEquiv (fun F ↦ F) (fun d ↦ p + d) (add_right_injective p)
    eEnd eLeft eRight fun F d a b ↦ ?_
  simp only [eEnd, eLeft, eRight, LinearEquiv.trans_apply, dgHomologyCompLeftEquiv_apply,
    dgHomologyCompRightEquiv_apply]
  rw [← dgHomologyComp_assoc k (pq := p + d) rfl (add_sub_cancel d n) (by omega) rfl u a b,
    dgHomologyComp_assoc k (qr := n - d + q) (by omega) rfl rfl (by omega) _ b v]
  simpa only [dgHomologyCastEquiv_rfl, LinearEquiv.refl_apply] using
    dgHomologyCastEquiv_dgHomologyComp k rfl (by omega : n - d + q = n - (p + d))
      (by omega : p + n + q = n) (by omega) (add_sub_cancel (p + d) n)
      (dgHomologyComp k E E' F rfl u a) (dgHomologyComp k F E' E rfl b v)

/-- Isomorphic objects in `DGHomotopyCategory k C` have equivalent `n`-sphericality. -/
theorem of_homotopyIso {E' : C} (hE : IsSphericalObject k n E)
    (e : DGHomotopyCategory.of k E ≅ DGHomotopyCategory.of k E') : IsSphericalObject k n E' :=
  hE.of_gradedEquiv (zero_add 0) e.hom e.inv
    (DGHomotopyCategory.dgHomologyComp_hom_inv k e)
    (DGHomotopyCategory.dgHomologyComp_inv_hom k e)

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
@[simp] theorem isSphericalObject_shiftFunctor_iff (n m : ℤ)
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
  exact ⟨fun hPm ↦ hPm.of_gradedEquiv (add_neg_cancel m) v u hvu huv,
    fun hP ↦ hP.of_gradedEquiv (neg_add_cancel m) u v huv hvu⟩

end DGTwistedObject

end TauCeti

namespace CategoryTheory.EnrichedFunctor

open TauCeti HomologicalComplex

universe v u₁ u₂

section Field

variable {k : Type v} [Field k] {C : Type u₁} {D : Type u₂} [DGCategory k C] [DGCategory k D]
  {F : EnrichedFunctor (CochainComplex (ModuleCat.{v} k) ℤ) C D}

/-- A quasi-fully faithful DG functor reflects `n`-spherical objects. -/
theorem IsQuasiFullyFaithful.isSphericalObject_of_obj (hff : F.IsQuasiFullyFaithful) {n : ℤ} {E : C}
    (hFE : IsSphericalObject k n (F.obj E)) : IsSphericalObject k n E :=
  hFE.of_homologyEquiv F.obj (fun d ↦ d) Function.injective_id (hff.homologyLinearEquiv E E)
    (fun X ↦ hff.homologyLinearEquiv E X) (fun X d ↦ hff.homologyLinearEquiv X E (n - d))
    fun _ d ↦ hff.homologyLinearEquiv_dgHomologyComp (add_sub_cancel d n)

/-- A DG quasi-equivalence preserves and reflects `n`-spherical objects. -/
theorem IsQuasiEquivalence.isSphericalObject_iff (hF : F.IsQuasiEquivalence) (n : ℤ) (E : C) :
    IsSphericalObject k n (F.obj E) ↔ IsSphericalObject k n E := by
  have hff := hF.isQuasiFullyFaithful
  refine ⟨hff.isSphericalObject_of_obj, fun hE ↦ ?_⟩
  choose X hX using hF.essentiallySurjective
  let eY (Y : D) := (hX Y).some
  let u (Y : D) : (dgHomComplex k (F.obj (X Y)) Y).homology 0 := (eY Y).hom
  let v (Y : D) : (dgHomComplex k Y (F.obj (X Y))).homology 0 := (eY Y).inv
  have huv (Y : D) : dgHomologyComp k (F.obj (X Y)) Y (F.obj (X Y)) (zero_add 0) (u Y) (v Y) =
      dgHomologyId k (F.obj (X Y)) := DGHomotopyCategory.dgHomologyComp_hom_inv k (eY Y)
  have hvu (Y : D) : dgHomologyComp k Y (F.obj (X Y)) Y (zero_add 0) (v Y) (u Y) =
      dgHomologyId k Y := DGHomotopyCategory.dgHomologyComp_inv_hom k (eY Y)
  refine hE.of_homologyEquiv X (fun d ↦ d) Function.injective_id
    (fun d ↦ (hff.homologyLinearEquiv E E d).symm)
    (fun Y d ↦ (dgHomologyCompRightEquiv k (F.obj E) (zero_add 0) (add_zero d)
      (v Y) (u Y) (hvu Y) (huv Y)).trans (hff.homologyLinearEquiv E (X Y) d).symm)
    (fun Y d ↦ (dgHomologyCompLeftEquiv k (F.obj E) (zero_add 0) (zero_add (n - d))
      (u Y) (v Y) (huv Y) (hvu Y)).trans (hff.homologyLinearEquiv (X Y) E (n - d)).symm)
    fun Y d a b ↦ (hff.homologyLinearEquiv E E n).injective ?_
  simp only [LinearEquiv.apply_symm_apply, hff.homologyLinearEquiv_dgHomologyComp,
    LinearEquiv.trans_apply, dgHomologyCompRightEquiv_apply, dgHomologyCompLeftEquiv_apply]
  rw [dgHomologyComp_assoc k (add_zero d) (zero_add (n - d)) (add_sub_cancel d n)
    (add_sub_cancel d n), ← dgHomologyComp_assoc k (zero_add 0) (zero_add (n - d))
    (zero_add (n - d)) (zero_add (n - d)), hvu Y, dgHomologyId_dgHomologyComp]

end Field

end CategoryTheory.EnrichedFunctor
