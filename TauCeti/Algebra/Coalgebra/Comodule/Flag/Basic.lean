/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Subcomodule.Coordinate
public import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# Flags of upper-triangular comodules

Let `M` be a finite free comodule with basis `b₀, ..., bₙ₋₁`. Its coefficient matrix is upper
triangular with diagonal `c` exactly when, for every `i`, the coaction of `bᵢ` is congruent to
`bᵢ ⊗ cᵢ` modulo the span of the preceding basis vectors. Thus the standard basis flag is
comodule-stable and its successive one-dimensional factors have weights `cᵢ`. The unitriangular
case `c = 1` says those factors are trivial.

This is the flag interface needed for the Kolchin inductions in Layer 5, "Unipotent groups", of
the ReductiveGroups roadmap. Once such an induction supplies successive fixed vectors, the
criterion here produces the upper-unitriangular coefficient matrix used to embed a faithful
representation into `Uₙ`.

## Main declarations

* `TauCeti.Comodule.coefficientMatrix_isUpperTriangular_and_diag_iff`: the
  quotient-by-preceding-span criterion for an upper-triangular coefficient matrix with prescribed
  diagonal.
* `TauCeti.Comodule.coefficientMatrix_isUpperUnitriangular_iff`: its unitriangular special case.
* `TauCeti.Comodule.coefficientMatrix_isUpperTriangular_iff`: stability of every initial
  basis span characterizes upper triangularity over a commutative semiring.
* `TauCeti.Comodule.flagSubcomodule`: the standard flag of an upper-triangular comodule, bundled as
  subcomodules.
* `TauCeti.Comodule.quotient_mk_basis_ne_zero`: each successive basis class is nonzero in the
  quotient by the preceding flag term.
* `TauCeti.Comodule.quotientCoact_flagSubcomodule_mk_basis`: each successive basis class has
  trivial coaction in that quotient.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

open scoped TensorProduct

namespace Module.Basis

/-- A complete flag spanned by subsets of a basis separates any two distinct basis vectors. -/
theorem exists_flag_separating {R M ι : Type*} [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {n : ℕ} (cb : Basis ι R M) (bas : Basis (Fin n) R M)
    (hcoord : ∀ r, bas.flag r = Submodule.span R (cb '' {j | cb j ∈ bas.flag r}))
    {a b : ι} (hab : a ≠ b) :
    ∃ r, ¬ (cb a ∈ bas.flag r ↔ cb b ∈ bas.flag r) := by
  classical
  by_contra! hsame
  have hex : ∃ r, cb a ∈ bas.flag r := ⟨Fin.last n, by simp⟩
  let r := Fin.find (fun r ↦ cb a ∈ bas.flag r) hex
  have har : cb a ∈ bas.flag r := Fin.find_spec hex
  have hr0 : r ≠ 0 := by
    intro hr
    simp [hr, cb.ne_zero a] at har
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i.succ = r := by
    refine ⟨⟨r.val - 1, by have := r.isLt; have := Fin.val_ne_zero_iff.mpr hr0; omega⟩, ?_⟩
    apply Fin.ext
    have := Fin.val_ne_zero_iff.mpr hr0
    simp only [Fin.val_succ]
    omega
  have ha : cb a ∉ bas.flag i.castSucc := by
    apply Fin.find_min hex
    -- The local r is the first flag term containing this basis vector.
    change i.castSucc < r
    rw [← hi]
    exact Fin.castSucc_lt_succ
  have hb : cb b ∉ bas.flag i.castSucc := fun h ↦ ha ((hsame _).mpr h)
  have har' : cb a ∈ bas.flag i.succ := by simpa only [hi] using har
  have hbr' : cb b ∈ bas.flag i.succ := (hsame _).mp har'
  have hzero (j : ι) (hj : cb j ∉ bas.flag i.castSucc) {z : M}
      (hz : z ∈ bas.flag i.castSucc) : cb.repr z j = 0 := by
    have hker : bas.flag i.castSucc ≤ LinearMap.ker (cb.coord j) := by
      rw [hcoord]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, hl, rfl⟩
      apply LinearMap.mem_ker.mpr
      have hjl : j ≠ l := by
        rintro rfl
        exact hj hl
      simp [Basis.coord_apply, hjl]
    simpa only [Basis.coord_apply] using LinearMap.mem_ker.mp (hker hz)
  rw [bas.flag_succ] at har' hbr'
  obtain ⟨va, hva, ua, hua, hsum_a⟩ := Submodule.mem_sup.mp har'
  obtain ⟨vb, hvb, ub, hub, hsum_b⟩ := Submodule.mem_sup.mp hbr'
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hva
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.mp hvb
  have hxa : x * cb.coord a (bas i) = 1 := by
    simpa [Basis.coord_apply, hzero a ha hua] using
      congrArg (cb.coord a) hsum_a
  have hxb : x * cb.coord b (bas i) = 0 := by
    simpa [Basis.coord_apply, hab, hab.symm, hzero b hb hua] using
      congrArg (cb.coord b) hsum_a
  have hya : y * cb.coord a (bas i) = 0 := by
    simpa [Basis.coord_apply, hab, hab.symm, hzero a ha hub] using
      congrArg (cb.coord a) hsum_b
  have hyb : y * cb.coord b (bas i) = 1 := by
    simpa [Basis.coord_apply, hzero b hb hub] using
      congrArg (cb.coord b) hsum_b
  apply one_ne_zero (α := R)
  calc
    1 = (x * cb.coord a (bas i)) * (y * cb.coord b (bas i)) := by rw [hxa, hyb, mul_one]
    _ = (x * cb.coord b (bas i)) * (y * cb.coord a (bas i)) := by ring
    _ = 0 := by rw [hxb, hya, mul_zero]

end Module.Basis

namespace TauCeti.Comodule

open Module

universe u v w

noncomputable section

variable {k : Type u} {H : Type v} {M : Type w} {n : ℕ}
variable [CommRing k] [AddCommMonoid H] [Module k H] [Coalgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]

/-- A coefficient matrix is upper triangular with prescribed diagonal exactly when each basis
vector has the prescribed coaction modulo the span of the preceding basis vectors. -/
theorem coefficientMatrix_isUpperTriangular_and_diag_iff (b : Basis (Fin n) k M) (c : Fin n → H) :
    ((coefficientMatrix (C := H) b).IsUpperTriangular ∧
        ∀ i : Fin n, coefficientMatrix (C := H) b i i = c i) ↔
      ∀ i : Fin n,
        TensorProduct.map (b.flag i.castSucc).mkQ (LinearMap.id : H →ₗ[k] H)
            (coact (C := H) (b i)) =
          Submodule.Quotient.mk (b i) ⊗ₜ[k] c i := by
  constructor
  · rintro ⟨htri, hdiag⟩ i
    rw [coact_basis_eq_sum_coefficientMatrix, map_sum]
    classical
    rw [Finset.sum_eq_single i]
    · simp [hdiag i]
    · intro j _ hji
      rcases lt_trichotomy j i with hji' | hji' | hij
      · rw [TensorProduct.map_tmul, LinearMap.id_apply]
        have hjflag : b j ∈ b.flag i.castSucc :=
          b.self_mem_flag (Fin.castSucc_lt_castSucc_iff.mpr hji')
        simp [(Submodule.Quotient.mk_eq_zero _).mpr hjflag]
      · exact (hji hji').elim
      · simp [htri hij]
    · simp
  · intro h
    have hcoeff (i j : Fin n) (hji : j ≤ i) :
        coefficientMatrix (C := H) b i j = if i = j then c i else 0 := by
      let q := (b.flag j.castSucc).mkQ
      let phi : (M ⧸ b.flag j.castSucc) →ₗ[k] k :=
        (b.flag j.castSucc).liftQ (b.coord i)
          (b.flag_le_ker_coord (Fin.castSucc_le_castSucc_iff.mpr hji))
      have heq := congrArg
        (fun z ↦ TensorProduct.lid k H
          (TensorProduct.map phi (LinearMap.id : H →ₗ[k] H) z)) (h j)
      rw [TensorProduct.map_map] at heq
      have hcomp : phi.comp q = b.coord i := by
        exact (b.flag j.castSucc).liftQ_mkQ (b.coord i) _
      rw [hcomp, LinearMap.id_comp] at heq
      rw [← matrixCoefficient_def] at heq
      rw [coefficientMatrix_apply]
      by_cases hij : i = j
      · subst i
        simpa [phi, q, Submodule.liftQ_apply, Basis.coord_apply] using heq
      · simpa [phi, q, Submodule.liftQ_apply, Basis.coord_apply, hij] using heq
    refine ⟨fun i j hji ↦ ?_, fun i ↦ ?_⟩
    · have hji' : j < i := by simpa only [id_eq] using hji
      simpa [hji'.ne'] using hcoeff i j hji'.le
    · simpa using hcoeff i i le_rfl

/-- A coefficient matrix is upper unitriangular exactly when each basis vector is fixed by the
coaction modulo the span of the preceding basis vectors. -/
theorem coefficientMatrix_isUpperUnitriangular_iff [One H] (b : Basis (Fin n) k M) :
    (coefficientMatrix (C := H) b).IsUpperUnitriangular ↔
      ∀ i : Fin n,
        TensorProduct.map (b.flag i.castSucc).mkQ (LinearMap.id : H →ₗ[k] H)
            (coact (C := H) (b i)) =
          Submodule.Quotient.mk (b i) ⊗ₜ[k] (1 : H) := by
  rw [Matrix.isUpperUnitriangular_def]
  exact coefficientMatrix_isUpperTriangular_and_diag_iff b fun _ ↦ 1

/-- The initial spans of a basis with upper-triangular coefficient matrix, bundled as
subcomodules. -/
def flagSubcomodule (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) (r : Fin (n + 1)) :
    Subcomodule k H M :=
  b.coordinateSpanSubcomodule {i | i.castSucc < r} <|
    (b.coordinateSpanIsStable_iff (C := H) _).2 <| by
    intro i hi j hj
    apply h
    exact Fin.castSucc_lt_castSucc_iff.mp (lt_of_lt_of_le hj (le_of_not_gt hi))

/-- The underlying submodule of `flagSubcomodule` is the corresponding basis flag. -/
@[simp]
theorem flagSubcomodule_toSubmodule (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) (r : Fin (n + 1)) :
    (flagSubcomodule (H := H) b h r).toSubmodule = b.flag r := by
  rw [flagSubcomodule, Basis.coordinateSpanSubcomodule_toSubmodule]
  rfl

/-- Membership in the bundled stable flag is membership in the corresponding basis flag. -/
@[simp]
theorem mem_flagSubcomodule_iff (bas : Basis (Fin n) k M)
    (htri : (coefficientMatrix (C := H) bas).IsUpperTriangular)
    (r : Fin (n + 1)) (x : M) :
    x ∈ flagSubcomodule bas htri r ↔ x ∈ bas.flag r := by
  rw [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule]

/-- A coordinate flag separating two basis vectors forces the corresponding coefficient to
vanish when every subcomodule containing the first vector contains the second. -/
theorem coefficient_eq_zero_of_coordinate_flag {ι : Type*} [Finite ι]
    (cb : Basis ι k M) (bas : Basis (Fin n) k M)
    (htri : (coefficientMatrix (C := H) bas).IsUpperTriangular)
    (hbas : ∀ r, bas.flag r = Submodule.span k (cb '' {i | cb i ∈ bas.flag r}))
    {a b : ι} (hab : a ≠ b)
    (hclosed : ∀ N : Subcomodule k H M, cb a ∈ N → cb b ∈ N) :
    coefficientMatrix (C := H) cb a b = 0 := by
  rcases subsingleton_or_nontrivial k with h | h
  · have : Subsingleton k := h
    calc
      _ = (1 : k) • coefficientMatrix (C := H) cb a b := (one_smul k _).symm
      _ = 0 := by rw [Subsingleton.elim (1 : k) 0, zero_smul]
  have : Nontrivial k := h
  classical
  let F := Comodule.flagSubcomodule bas htri
  have hcoord (r : Fin (n + 1)) :
      (F r).toSubmodule = Submodule.span k (cb '' {i | cb i ∈ F r}) := by
    rw [Comodule.flagSubcomodule_toSubmodule]
    simpa only [F, mem_flagSubcomodule_iff] using hbas r
  obtain ⟨r, hr⟩ := cb.exists_flag_separating bas hbas hab
  have hforward : cb a ∈ F r → cb b ∈ F r := hclosed (F r)
  have hr' : ¬ (cb a ∈ F r ↔ cb b ∈ F r) := by
    simpa only [F, mem_flagSubcomodule_iff] using hr
  have hnot : cb a ∉ F r := by
    intro ha
    exact hr' ⟨fun _ ↦ hforward ha, fun _ ↦ ha⟩
  have hmem : cb b ∈ F r := by
    by_contra hb
    exact hr' ⟨fun ha ↦ False.elim (hnot ha), fun h ↦ False.elim (hb h)⟩
  exact Module.Basis.coefficient_eq_zero_of_coordinate_subcomodule cb {i | cb i ∈ F r}
    (F r) (hcoord r) hnot hmem

/-- The coaction of a basis vector in a stable initial segment belongs to the tensor product of
that initial segment with the coalgebra. -/
theorem coact_basis_mem_flag (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular)
    {i : Fin n} {r : Fin (n + 1)} (hir : i.castSucc < r) :
    coact (C := H) (b i) ∈
      LinearMap.range
        (TensorProduct.map (b.flag r).subtype (LinearMap.id : H →ₗ[k] H)) := by
  have hbi : b i ∈ flagSubcomodule (H := H) b h r := by
    rw [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule]
    exact b.self_mem_flag hir
  rw [← flagSubcomodule_toSubmodule b h r]
  exact (flagSubcomodule (H := H) b h r).coact_mem hbi

/-- The first term of the bundled basis flag is the zero subcomodule. -/
@[simp]
theorem flagSubcomodule_zero (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    flagSubcomodule (H := H) b h 0 = ⊥ := by
  ext m
  simp only [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule,
    Basis.flag_zero, Subcomodule.bot_toSubmodule, Submodule.mem_bot]

/-- The last term of the bundled basis flag is the full comodule. -/
@[simp]
theorem flagSubcomodule_last (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    flagSubcomodule (H := H) b h (.last n) = ⊤ := by
  ext m
  simp only [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule,
    Basis.flag_last, Subcomodule.top_toSubmodule, Submodule.mem_top]

/-- The bundled basis flag is monotone. -/
theorem flagSubcomodule_monotone (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    Monotone (flagSubcomodule (H := H) b h) := by
  intro r s hrs m hm
  rw [← Subcomodule.mem_toSubmodule, flagSubcomodule_toSubmodule] at hm ⊢
  exact b.flag_mono hrs hm

/-- The bundled basis flag is strictly monotone. -/
theorem flagSubcomodule_strictMono (b : Basis (Fin n) k M)
    [Nontrivial k] (h : (coefficientMatrix (C := H) b).IsUpperTriangular) :
    StrictMono (flagSubcomodule (H := H) b h) := by
  intro r s hrs
  refine lt_of_le_of_ne (flagSubcomodule_monotone b h hrs.le) ?_
  intro hrs'
  have hflags := congrArg Subcomodule.toSubmodule hrs'
  rw [flagSubcomodule_toSubmodule, flagSubcomodule_toSubmodule] at hflags
  exact (b.flag_strictMono hrs).ne hflags

/-- A basis vector does not vanish in the quotient by the span of its predecessors. -/
theorem quotient_mk_basis_ne_zero [Nontrivial k] (b : Basis (Fin n) k M) (i : Fin n) :
    (Submodule.Quotient.mk (b i) : M ⧸ b.flag i.castSucc) ≠ 0 := by
  rw [ne_eq, Submodule.Quotient.mk_eq_zero, b.self_mem_flag_iff]
  exact lt_irrefl i.castSucc

/-- In the quotient by the preceding term of an upper-unitriangular basis flag, the class of the
next basis vector has trivial coaction. -/
theorem quotientCoact_flagSubcomodule_mk_basis
    [One H]
    (b : Basis (Fin n) k M)
    (h : (coefficientMatrix (C := H) b).IsUpperUnitriangular) (i : Fin n) :
    let N := flagSubcomodule (H := H) b h.isUpperTriangular i.castSucc
    N.quotientCoact (Submodule.Quotient.mk (b i)) =
      Submodule.Quotient.mk (b i) ⊗ₜ[k] (1 : H) := by
  dsimp only
  rw [Subcomodule.quotientCoact_mk, flagSubcomodule_toSubmodule]
  exact (coefficientMatrix_isUpperUnitriangular_iff b).mp h i

end

section Semiring

variable {R C V : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid V] [Module R V] [Comodule R C V] {n : ℕ}

/-- A coefficient matrix is upper triangular exactly when every initial basis span is the
underlying submodule of a subcomodule. -/
theorem coefficientMatrix_isUpperTriangular_iff (b : Basis (Fin n) R V) :
    (coefficientMatrix (C := C) b).IsUpperTriangular ↔
      ∀ r : Fin (n + 1), ∃ N : Subcomodule R C V, N.toSubmodule = b.flag r := by
  constructor
  · intro h r
    have hs : b.coordinateSpanIsStable (C := C) {a | a.castSucc < r} := by
      rw [b.coordinateSpanIsStable_iff]
      intro i hi j hj
      apply h
      exact Fin.castSucc_lt_castSucc_iff.mp (lt_of_lt_of_le hj (le_of_not_gt hi))
    exact ⟨b.coordinateSpanSubcomodule _ hs, b.coordinateSpanSubcomodule_toSubmodule _ hs⟩
  · intro h i j hji
    obtain ⟨N, hN⟩ := h j.succ
    have hs := (b.exists_subcomodule_toSubmodule_eq_span_iff_coordinateSpanIsStable
      {a | a.castSucc < j.succ}).mp ⟨N, hN⟩
    rw [b.coordinateSpanIsStable_iff] at hs
    exact hs i (by simpa only [Set.mem_ofPred_eq, Fin.castSucc_lt_succ_iff, id_eq] using
      (not_le_of_gt hji)) j (by simp)

end Semiring

end TauCeti.Comodule
