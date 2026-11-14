/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Data.Finsupp.Diagram
public import TauCeti.RingTheory.MvPolynomial.Finrank
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.FiniteType
import TauCeti.Data.Finsupp.Fin
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Bierstone–Milman's finite-degree criterion and homogeneous diagram division

Given a diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ`, a commutative
ring `A`, and a family `H : D.diagramVertices → MvPolynomial σ A` of homogeneous polynomials with
`(H v).IsHomogeneous v.1.degree`, Bierstone and Milman (1997, §8, pp. 274–275) consider in each
degree `ℓ : ℕ` the finite family `D.diagramSpanSet H ℓ` (`P(ℓ)`) consisting of:

* the supported monomial multiples `monomial β 1 * H v` with `β ∈ D.diagramBox v.1` and
  `v.1.degree + β.degree = ℓ`, and
* the complementary monomials `monomial γ 1` with `γ ∉ D` and `γ.degree = ℓ`.

**Theorem 8.1 (`Set.span_diagramSpanSet_eq_of_le`)** states that when `D` is upward closed and
monotone (`D.IsMonotoneDiagram`), if `D.diagramSpanSet H k` spans `homogeneousSubmodule σ A k` at
some degree `k ≥ D.diagramCutoff`, then `D.diagramSpanSet H ℓ` spans `homogeneousSubmodule σ A ℓ`
for every `ℓ ≥ k`.

When `D` is upward closed, the partition of `{δ : σ →₀ ℕ // δ.degree = ℓ}` into `Dᶜ` and the
disjoint vertex cells `D.diagramCell v.1` defines an `A`-linear endomorphism
`D.diagramDivisionEnd H hH ℓ` of the finite free `A`-module `homogeneousSubmodule σ A ℓ` sending
each monomial basis element to the corresponding element of `D.diagramSpanSet H ℓ`. By the Orzech
property of commutative rings and Cramer's rule (`LinearMap.isUnit_iff_isUnit_det`), spanning in
degree `ℓ`, invertibility of `LinearMap.det (D.diagramDivisionEnd H hH ℓ)`, and existence and
uniqueness of homogeneous supported division in degree `ℓ` are all equivalent
(`Set.existsUnique_homogeneous_division_iff_span_eq`,
`Set.isUnit_det_diagramDivisionEnd_iff_span_eq`). For an upward-closed monotone diagram `D`, these
conditions hold in *every* degree `ℓ : ℕ` if and only if the single finite-jet determinant product
`D.diagramCutoffDet H hH` across degrees `ℓ ≤ D.diagramCutoff` is a unit in `A`
(`Set.isUnit_diagramCutoffDet_iff_forall_span_eq`), and therefore hold in every degree after any
ring homomorphism (such as `Localization.Away`) that inverts `D.diagramCutoffDet H hH`
(`Set.existsUnique_homogeneous_division_of_isUnit_map_diagramCutoffDet`, Bierstone–Milman, p. 282).

## Main definitions

* `Set.diagramSpanSet`: the degree-`ℓ` family `P(ℓ)` of supported multiples `Y^β H_v` and
  complementary monomials `Y^γ` (`γ ∉ D`).
* `Set.diagramDivisionEnd`: the degree-`ℓ` homogeneous supported-division endomorphism on
  `homogeneousSubmodule σ A ℓ`.
* `Set.diagramCutoffDet`: the product of `LinearMap.det (D.diagramDivisionEnd H hH ℓ)` for
  `ℓ ≤ D.diagramCutoff`.

## Main results

* `Set.span_diagramSpanSet_eq_of_le`: Bierstone–Milman's finite-degree criterion (Theorem 8.1).
* `Set.isUnit_det_diagramDivisionEnd_iff_span_eq`,
  `Set.existsUnique_homogeneous_division_iff_span_eq`: equivalence of spanning, unit block
  determinant, and unique homogeneous supported division in degree `ℓ`.
* `Set.isUnit_diagramCutoffDet_iff_forall_span_eq`,
  `Set.existsUnique_homogeneous_division_of_isUnit_map_diagramCutoffDet`: finite-jet determinantal
  criterion and base-change / localization extension of unique homogeneous supported division to
  all degrees.
* `Set.span_diagramSpanSet_empty`, `Set.span_diagramSpanSet_univ_zero_iff`,
  `Set.span_diagramSpanSet_Ici_single_fin_one_iff`,
  `Set.exists_monotone_diagram_span_lt_diagramCutoff_not_span`: boundary cases (`D = ∅`,
  `D = Set.univ`, one-variable cones) and sharpness of `Set.diagramCutoff` in two variables.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Theorem 8.1 and Definition 8.3, pp. 274–275; proof of Theorem 9.6, p. 282.
-/

public section

open MvPolynomial

namespace Set

section SpanSet

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommSemiring A]

/-- Bierstone–Milman's degree-`ℓ` homogeneous division family
`P(ℓ) = {Y^β H_v : β ∈ □_v, |v| + |β| = ℓ} ∪ {Y^γ : γ ∉ D, |γ| = ℓ}`. -/
def diagramSpanSet (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    Set (MvPolynomial σ A) :=
  {p | ∃ (v : D.diagramVertices) (β : σ →₀ ℕ),
      β ∈ D.diagramBox v.1 ∧ v.1.degree + β.degree = ℓ ∧ p = monomial β 1 * H v} ∪
    {p | ∃ γ ∉ D, γ.degree = ℓ ∧ p = monomial γ 1}

theorem mem_diagramSpanSet_iff {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    {ℓ : ℕ} {p : MvPolynomial σ A} :
    p ∈ D.diagramSpanSet H ℓ ↔
      (∃ (v : D.diagramVertices) (β : σ →₀ ℕ),
        β ∈ D.diagramBox v.1 ∧ v.1.degree + β.degree = ℓ ∧ p = monomial β 1 * H v) ∨
      (∃ γ ∉ D, γ.degree = ℓ ∧ p = monomial γ 1) :=
  Iff.rfl

theorem monomial_mul_mem_diagramSpanSet {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} {ℓ : ℕ} (v : D.diagramVertices) {β : σ →₀ ℕ}
    (hβ : β ∈ D.diagramBox v.1) (hdeg : v.1.degree + β.degree = ℓ) :
    monomial β 1 * H v ∈ D.diagramSpanSet H ℓ :=
  Or.inl ⟨v, β, hβ, hdeg, rfl⟩

theorem monomial_mem_diagramSpanSet {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} {ℓ : ℕ} {γ : σ →₀ ℕ} (hγ : γ ∉ D)
    (hdeg : γ.degree = ℓ) :
    monomial γ 1 ∈ D.diagramSpanSet H ℓ :=
  Or.inr ⟨γ, hγ, hdeg, rfl⟩

theorem isHomogeneous_of_mem_diagramSpanSet {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} {p : MvPolynomial σ A} (hp : p ∈ D.diagramSpanSet H ℓ) :
    p.IsHomogeneous ℓ := by
  rcases hp with ⟨v, β, _, hdeg, rfl⟩ | ⟨γ, _, rfl, rfl⟩
  · rw [← hdeg, add_comm]
    exact (isHomogeneous_monomial 1 (by simp [Finsupp.degree_apply])).mul (hH v)
  · exact isHomogeneous_monomial 1 (by simp [Finsupp.degree_apply])

theorem span_diagramSpanSet_le_homogeneousSubmodule {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    (ℓ : ℕ) :
    Submodule.span A (D.diagramSpanSet H ℓ) ≤ homogeneousSubmodule σ A ℓ :=
  Submodule.span_le.mpr fun _ hp ↦
    (mem_homogeneousSubmodule ℓ _).mpr (isHomogeneous_of_mem_diagramSpanSet hH hp)

private theorem image_renameEquiv_diagramSpanSet_subset {τ : Type*} [Finite τ] [LinearOrder τ]
    (e : τ ≃o σ) (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (renameEquiv A e.toEquiv) ''
        ((Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramSpanSet
          (fun v₀ ↦ (renameEquiv A e.toEquiv).symm
            (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
              (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩)) ℓ) ⊆
      D.diagramSpanSet H ℓ := by
  rintro _ ⟨q, hq, rfl⟩
  rcases hq with ⟨v₀, β₀, hβ₀, hdeg₀, rfl⟩ | ⟨γ₀, hγ₀, hdeg₀, rfl⟩
  · have hβ : Finsupp.equivMapDomain e.toEquiv β₀ ∈
        D.diagramBox (Finsupp.equivMapDomain e.toEquiv v₀.1) :=
      (mem_diagramBox_preimage_equivMapDomain_iff e).mp hβ₀
    have hdeg : (Finsupp.equivMapDomain e.toEquiv v₀.1).degree +
        (Finsupp.equivMapDomain e.toEquiv β₀).degree = ℓ := by
      simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg₀
    rw [map_mul, AlgEquiv.apply_symm_apply, renameEquiv_apply, rename_monomial,
      ← Finsupp.equivMapDomain_eq_mapDomain]
    exact monomial_mul_mem_diagramSpanSet (H := H)
      ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
        (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩ hβ hdeg
  · have hdeg : (Finsupp.equivMapDomain e.toEquiv γ₀).degree = ℓ := by
      simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg₀
    rw [renameEquiv_apply, rename_monomial, ← Finsupp.equivMapDomain_eq_mapDomain]
    exact monomial_mem_diagramSpanSet (H := H) hγ₀ hdeg

/-- Relabeling variables along an order isomorphism `e : τ ≃o σ` transports `diagramSpanSet`. -/
theorem image_renameEquiv_diagramSpanSet {τ : Type*} [Finite τ] [LinearOrder τ] (e : τ ≃o σ)
    (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (renameEquiv A e.toEquiv) ''
        ((Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramSpanSet
          (fun v₀ ↦ (renameEquiv A e.toEquiv).symm
            (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
              (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩)) ℓ) =
      D.diagramSpanSet H ℓ := by
  refine Subset.antisymm (image_renameEquiv_diagramSpanSet_subset e D H ℓ) ?_
  rintro _ (⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
  · obtain ⟨v₀_val, hv₀_eq⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective v.1
    simp only [Finsupp.domCongr_apply] at hv₀_eq
    obtain ⟨β₀, hβ₀_eq⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective β
    simp only [Finsupp.domCongr_apply] at hβ₀_eq
    have hv₀ : v₀_val ∈ (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramVertices :=
      (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mpr (hv₀_eq.symm ▸ v.2)
    have hβ₀ : β₀ ∈ (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramBox v₀_val :=
      (mem_diagramBox_preimage_equivMapDomain_iff e).mpr (hv₀_eq.symm ▸ hβ₀_eq.symm ▸ hβ)
    have hdeg₀ : v₀_val.degree + β₀.degree = ℓ := by
      have hv_d : v.1.degree = v₀_val.degree := by
        rw [← hv₀_eq, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]
      have hβ_d : β.degree = β₀.degree := by
        rw [← hβ₀_eq, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]
      omega
    refine ⟨monomial β₀ 1 * _, monomial_mul_mem_diagramSpanSet ⟨v₀_val, hv₀⟩ hβ₀ hdeg₀, ?_⟩
    have hv_sub : (⟨Finsupp.equivMapDomain e.toEquiv v₀_val,
        (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp hv₀⟩ :
        D.diagramVertices) = v := Subtype.ext hv₀_eq
    rw [map_mul, AlgEquiv.apply_symm_apply, hv_sub, renameEquiv_apply, rename_monomial,
      ← Finsupp.equivMapDomain_eq_mapDomain, hβ₀_eq]
  · obtain ⟨γ₀, hγ₀_eq⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective γ
    simp only [Finsupp.domCongr_apply] at hγ₀_eq
    have hγ₀ : γ₀ ∉ Finsupp.equivMapDomain e.toEquiv ⁻¹' D := fun hm ↦ hγ (hγ₀_eq ▸ hm)
    have hdeg₀ : γ₀.degree = ℓ := by
      rw [← hdeg, ← hγ₀_eq, Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]
    refine ⟨monomial γ₀ 1, monomial_mem_diagramSpanSet hγ₀ hdeg₀, ?_⟩
    simp [← hγ₀_eq, renameEquiv_apply, rename_monomial, Finsupp.equivMapDomain_eq_mapDomain]

theorem diagramSpanSet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ =
      {p | ∃ γ : σ →₀ ℕ, γ.degree = ℓ ∧ p = monomial γ 1} := by
  ext p
  simp only [mem_diagramSpanSet_iff, notMem_empty, not_false_eq_true, true_and, mem_ofPred,
    or_iff_right_iff_imp]
  rintro ⟨⟨v, hv⟩, _⟩
  simp at hv

/-- For `D = ∅`, the complementary monomials span every homogeneous degree independently of `H`. -/
@[simp]
theorem span_diagramSpanSet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (ℓ : ℕ) :
    Submodule.span A ((∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  apply le_antisymm
  · refine span_diagramSpanSet_le_homogeneousSubmodule (fun ⟨v, hv⟩ ↦ ?_) ℓ
    simp at hv
  · intro p hp
    rw [diagramSpanSet_empty]
    have hp_hom : p.IsHomogeneous ℓ := (mem_homogeneousSubmodule ℓ p).mp hp
    rw [p.as_sum]
    refine Submodule.sum_mem _ fun γ hγ ↦ ?_
    have hdeg : γ.degree = ℓ := by
      rw [Finsupp.degree_apply]
      exact (hp_hom.degree_eq_sum_deg_support hγ).symm
    have hsmul : p.coeff γ • monomial γ (1 : A) = monomial γ (p.coeff γ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, hdeg, rfl⟩)

end SpanSet

section FiniteDegreeCriterion

variable {A : Type*} [CommRing A]

/-- Above `D.diagramCutoff`, multiplying any generator in `D.diagramSpanSet H m` by `X 0` yields a
generator in `D.diagramSpanSet H (m + 1)`. -/
private theorem X_zero_mul_mem_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hm : D.diagramCutoff ≤ m)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ D.diagramSpanSet H m) :
    X 0 * g ∈ D.diagramSpanSet H (m + 1) := by
  rcases hg with ⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
  · have hmul : X 0 * (monomial β 1 * H v) = monomial (Finsupp.single 0 1 + β) 1 * H v := by
      rw [← mul_assoc, X, monomial_mul_monomial, mul_one]
    rw [hmul]
    refine monomial_mul_mem_diagramSpanSet v
      (single_zero_add_mem_diagramBox hD_mono hβ (hdeg ▸ hm)) ?_
    rw [map_add, Finsupp.degree_single]
    omega
  · have hmul : X 0 * monomial γ (1 : A) = monomial (Finsupp.single 0 1 + γ) 1 := by
      rw [X, monomial_mul_monomial, mul_one]
    rw [hmul]
    refine monomial_mem_diagramSpanSet
      (single_zero_add_notMem_of_notMem hD_up hD_mono hγ (hdeg ▸ hm)) ?_
    rw [map_add, Finsupp.degree_single, hdeg, add_comm]

private theorem X_zero_mul_mem_span_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hm : D.diagramCutoff ≤ m)
    (hspan_m : homogeneousSubmodule (Fin (n + 1)) A m ≤ Submodule.span A (D.diagramSpanSet H m))
    {Q : MvPolynomial (Fin (n + 1)) A} (hQ : Q.IsHomogeneous m) :
    X 0 * Q ∈ Submodule.span A (D.diagramSpanSet H (m + 1)) := by
  have hQ_mem : Q ∈ Submodule.span A (D.diagramSpanSet H m) :=
    hspan_m ((mem_homogeneousSubmodule m Q).mpr hQ)
  have hmap : X 0 * Q ∈
      (Submodule.span A (D.diagramSpanSet H m)).map (LinearMap.mulLeft A (X 0)) :=
    Submodule.mem_map_of_mem hQ_mem
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span (X_zero_mul_mem_diagramSpanSet hD_up hD_mono hm hg)

private theorem aeval_cons_zero_mem_span_diagramSliceZero {n k : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hk : D.diagramCutoff ≤ k)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ D.diagramSpanSet H k) :
    aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X) g ∈
      Submodule.span A
        (D.diagramSliceZero.diagramSpanSet
          (fun v' ↦ aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X)
            (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩)) k) := by
  rcases hg with ⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
  · rw [map_mul, aeval_cons_zero_monomial]
    split_ifs with hβ0
    · by_cases hv0 : v.1 0 = 0
      · have hv_eq : Finsupp.cons 0 v.1.tail = v.1 := by rw [← hv0, Finsupp.cons_tail]
        have hβ_eq : Finsupp.cons 0 β.tail = β := by rw [← hβ0, Finsupp.cons_tail]
        have hv' : v.1.tail ∈ D.diagramSliceZero.diagramVertices :=
          mem_diagramVertices_diagramSliceZero_iff.mpr (hv_eq.symm ▸ v.2)
        have hβ' : β.tail ∈ D.diagramSliceZero.diagramBox v.1.tail :=
          cons_zero_mem_diagramBox_iff.mp (hv_eq.symm ▸ hβ_eq.symm ▸ hβ)
        have hdeg' : v.1.tail.degree + β.tail.degree = k := by
          have hv_deg : v.1.degree = v.1.tail.degree := by
            simpa using (congrArg Finsupp.degree hv_eq).symm
          have hβ_deg : β.degree = β.tail.degree := by
            simpa using (congrArg Finsupp.degree hβ_eq).symm
          omega
        have hv_sub : (⟨Finsupp.cons 0 v.1.tail,
            mem_diagramVertices_diagramSliceZero_iff.mp hv'⟩ : D.diagramVertices) = v :=
          Subtype.ext hv_eq
        rw [← hv_sub]
        exact Submodule.subset_span (monomial_mul_mem_diagramSpanSet ⟨v.1.tail, hv'⟩ hβ' hdeg')
      · exfalso
        have hlt := degree_add_lt_diagramCutoff_of_mem_diagramBox hD_mono v.2
          (Nat.pos_of_ne_zero hv0) hβ hβ0
        omega
    · rw [zero_mul]
      exact zero_mem _
  · rw [aeval_cons_zero_monomial]
    split_ifs with hγ0
    · have hγ_eq : Finsupp.cons 0 γ.tail = γ := by rw [← hγ0, Finsupp.cons_tail]
      have hγ' : γ.tail ∉ D.diagramSliceZero :=
        fun hm ↦ hγ (hγ_eq ▸ D.mem_diagramSliceZero_iff.mp hm)
      have hdeg' : γ.tail.degree = k := by
        simpa [hdeg] using congrArg Finsupp.degree hγ_eq
      exact Submodule.subset_span (monomial_mem_diagramSpanSet hγ' hdeg')
    · exact zero_mem _

/-- Above `D.diagramCutoff`, spanning of `homogeneousSubmodule (Fin (n + 1)) A k` by
`D.diagramSpanSet H k` descends to `D.diagramSliceZero` on `Fin n`. -/
private theorem span_diagramSliceZero_of_span {n k : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hk : D.diagramCutoff ≤ k)
    (hspan : homogeneousSubmodule (Fin (n + 1)) A k ≤ Submodule.span A (D.diagramSpanSet H k)) :
    homogeneousSubmodule (Fin n) A k ≤
      Submodule.span A
        (D.diagramSliceZero.diagramSpanSet
          (fun v' ↦ aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X)
            (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩)) k) := by
  intro q hq
  have hq_hom : (rename Fin.succ q).IsHomogeneous k :=
    (IsHomogeneous.rename_isHomogeneous_iff (Fin.succ_injective n)).mpr
      ((mem_homogeneousSubmodule k q).mp hq)
  have hmap := Submodule.mem_map_of_mem
    (f := (aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X)).toLinearMap)
    (hspan ((mem_homogeneousSubmodule k _).mpr hq_hom))
  have heval_q : aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X) (rename Fin.succ q) = q := by
    have hcomp : Fin.cons (0 : MvPolynomial (Fin n) A) X ∘ Fin.succ = X := by ext i; simp
    rw [aeval_rename, hcomp, aeval_X_left, AlgHom.id_apply]
  rw [AlgHom.toLinearMap_apply, heval_q, Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨g, hg, rfl⟩
  exact aeval_cons_zero_mem_span_diagramSliceZero hD_mono hk hg

/-- Lifting any slice generator of degree `m + 1` along `Fin.succ` lands in
`Submodule.span A (D.diagramSpanSet H (m + 1))` once degree `m` spans. -/
private theorem rename_succ_mem_span_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) (hm : D.diagramCutoff ≤ m)
    (ihm : homogeneousSubmodule (Fin (n + 1)) A m ≤ Submodule.span A (D.diagramSpanSet H m))
    {g' : MvPolynomial (Fin n) A}
    (hg' : g' ∈ D.diagramSliceZero.diagramSpanSet
      (fun v' ↦ aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X)
        (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩)) (m + 1)) :
    rename Fin.succ g' ∈ Submodule.span A (D.diagramSpanSet H (m + 1)) := by
  rcases hg' with ⟨v', β', hβ', hdeg', rfl⟩ | ⟨γ', hγ', hdeg', rfl⟩
  · let v : D.diagramVertices :=
      ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩
    let Q : MvPolynomial (Fin (n + 1)) A := monomial (Finsupp.cons 0 β') 1 * H v
    have hQ_mem : Q ∈ D.diagramSpanSet H (m + 1) :=
      monomial_mul_mem_diagramSpanSet v (cons_zero_mem_diagramBox_iff.mpr hβ') (by simpa [v])
    obtain ⟨R, hR_hom, hQ_split⟩ :=
      (isHomogeneous_of_mem_diagramSpanSet hH hQ_mem).exists_eq_rename_succ_add_X_zero_mul
    have hkQ : aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X) Q =
        monomial β' 1 *
          aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X) (H v) := by
      simp [Q, map_mul, aeval_cons_zero_monomial]
    rw [hkQ] at hQ_split
    have hrel : rename Fin.succ
        (monomial β' 1 * aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X) (H v)) =
        Q - X 0 * R := eq_sub_of_add_eq hQ_split
    rw [hrel]
    exact sub_mem (Submodule.subset_span hQ_mem)
      (X_zero_mul_mem_span_diagramSpanSet hD_up hD_mono hm ihm hR_hom)
  · rw [rename_monomial, Finsupp.mapDomain_finSucc]
    exact Submodule.subset_span
      (monomial_mem_diagramSpanSet (mt D.mem_diagramSliceZero_iff.mpr hγ') (by simpa using hdeg'))

/-- Finite-degree criterion on `Fin d` (induction on the number of variables `d`). -/
private theorem homogeneousSubmodule_le_span_fin :
    ∀ {d : ℕ} {D : Set (Fin d →₀ ℕ)} (_hD_up : IsUpperSet D) (_hD_mono : D.IsMonotoneDiagram)
      {H : D.diagramVertices → MvPolynomial (Fin d) A}
      (_hH : ∀ v, (H v).IsHomogeneous v.1.degree)
      {k : ℕ} (_hk : D.diagramCutoff ≤ k)
      (_hspan : homogeneousSubmodule (Fin d) A k ≤ Submodule.span A (D.diagramSpanSet H k))
      {ℓ : ℕ} (_hℓ : k ≤ ℓ),
      homogeneousSubmodule (Fin d) A ℓ ≤ Submodule.span A (D.diagramSpanSet H ℓ)
  | 0, _, _, _, _, _, _, _, hspan, ℓ, hℓ => by
    rcases hℓ.eq_or_lt with rfl | hlt
    · exact hspan
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hlt)
      rw [MvPolynomial.homogeneousSubmodule_succ_eq_bot_of_isEmpty]
      exact bot_le
  | n + 1, D, hD_up, hD_mono, H, hH, k, hk, hspan, ℓ, hℓ => by
    let H' : D.diagramSliceZero.diagramVertices → MvPolynomial (Fin n) A :=
      fun v' ↦ aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X)
        (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩)
    have hH' : ∀ v', (H' v').IsHomogeneous v'.1.degree := fun v' ↦ by
      have hdeg : (Finsupp.cons 0 v'.1).degree = v'.1.degree := by simp
      simpa [H', hdeg] using
        (hH ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩).aeval_cons_zero
    have hspan' (m : ℕ) (hm : k ≤ m) :
        homogeneousSubmodule (Fin n) A m ≤
          Submodule.span A (D.diagramSliceZero.diagramSpanSet H' m) :=
      homogeneousSubmodule_le_span_fin hD_up.diagramSliceZero hD_mono.diagramSliceZero hH'
        ((diagramSliceZero_diagramCutoff_le D).trans hk)
        (span_diagramSliceZero_of_span hD_mono hk hspan) hm
    induction ℓ, hℓ using Nat.le_induction with
    | base => exact hspan
    | succ m hm ihm =>
      intro P hP
      obtain ⟨Q, hQ_hom, hP_split⟩ :=
        ((mem_homogeneousSubmodule (m + 1) P).mp hP).exists_eq_rename_succ_add_X_zero_mul
      rw [← hP_split]
      refine add_mem ?_ (X_zero_mul_mem_span_diagramSpanSet hD_up hD_mono (hk.trans hm) ihm hQ_hom)
      have hkP : aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X) P ∈
          Submodule.span A (D.diagramSliceZero.diagramSpanSet H' (m + 1)) :=
        hspan' (m + 1) (hm.trans (Nat.le_succ m))
          ((mem_homogeneousSubmodule (m + 1) _).mpr
            ((mem_homogeneousSubmodule (m + 1) P).mp hP).aeval_cons_zero)
      have hmap := Submodule.mem_map_of_mem (f := (rename (R := A) Fin.succ).toLinearMap) hkP
      rw [AlgHom.toLinearMap_apply, Submodule.map_span] at hmap
      refine (Submodule.span_le.mpr ?_) hmap
      rintro _ ⟨g', hg', rfl⟩
      exact rename_succ_mem_span_diagramSpanSet hD_up hD_mono hH (hk.trans hm) ihm hg'

private theorem homogeneousSubmodule_le_span_preimage_equivMapDomain_iff
    {σ τ : Type*} [Finite σ] [LinearOrder σ] [Finite τ] [LinearOrder τ] (e : τ ≃o σ)
    (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A) (m : ℕ) :
    homogeneousSubmodule τ A m ≤
        Submodule.span A ((Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramSpanSet
          (fun v₀ ↦ (renameEquiv A e.toEquiv).symm
            (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
              (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩)) m) ↔
      homogeneousSubmodule σ A m ≤ Submodule.span A (D.diagramSpanSet H m) := by
  have hmap_span : Submodule.span A (D.diagramSpanSet H m) =
      (Submodule.span A ((Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramSpanSet
        (fun v₀ ↦ (renameEquiv A e.toEquiv).symm
          (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
            (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩)) m)).map
        (renameEquiv A e.toEquiv).toLinearMap := by
    rw [Submodule.map_span]
    exact congrArg (Submodule.span A) (image_renameEquiv_diagramSpanSet e D H m).symm
  constructor
  · intro hle p hp
    have hinj_symm : Function.Injective e.toEquiv.symm := e.symm.injective
    have hp₀_hom : ((renameEquiv A e.toEquiv).symm p).IsHomogeneous m := by
      rw [renameEquiv_symm, renameEquiv_apply, IsHomogeneous.rename_isHomogeneous_iff hinj_symm]
      exact (mem_homogeneousSubmodule m p).mp hp
    have hmem := Submodule.mem_map_of_mem (f := (renameEquiv A e.toEquiv).toLinearMap)
      (hle ((mem_homogeneousSubmodule m _).mpr hp₀_hom))
    rw [AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply] at hmem
    rwa [hmap_span]
  · intro hle q hq
    have hinj : Function.Injective e.toEquiv := e.injective
    have hq_hom : ((renameEquiv A e.toEquiv) q).IsHomogeneous m := by
      rw [renameEquiv_apply, IsHomogeneous.rename_isHomogeneous_iff hinj]
      exact (mem_homogeneousSubmodule m q).mp hq
    have hmem : (renameEquiv A e.toEquiv) q ∈ Submodule.span A (D.diagramSpanSet H m) :=
      hle ((mem_homogeneousSubmodule m _).mpr hq_hom)
    rw [hmap_span] at hmem
    obtain ⟨q', hq', heq⟩ := Submodule.mem_map.mp hmem
    rwa [(renameEquiv A e.toEquiv).injective heq] at hq'

/-- **Bierstone–Milman's Finite-Degree Criterion** (inclusion form, Theorem 8.1): for an
upward-closed monotone diagram `D` on a finite linearly ordered variable set `σ`, if
`D.diagramSpanSet H k` spans `homogeneousSubmodule σ A k` at some `k ≥ D.diagramCutoff`, then it
spans `homogeneousSubmodule σ A ℓ` for every `ℓ ≥ k`. -/
theorem homogeneousSubmodule_le_span_diagramSpanSet_of_le {σ : Type*} [Finite σ] [LinearOrder σ]
    {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {k : ℕ} (hk : D.diagramCutoff ≤ k)
    (hspan : homogeneousSubmodule σ A k ≤ Submodule.span A (D.diagramSpanSet H k))
    {ℓ : ℕ} (hℓ : k ≤ ℓ) :
    homogeneousSubmodule σ A ℓ ≤ Submodule.span A (D.diagramSpanSet H ℓ) := by
  cases nonempty_fintype σ
  let e : Fin (Fintype.card σ) ≃o σ := Fintype.orderIsoFinOfCardEq σ rfl
  let D₀ : Set (Fin (Fintype.card σ) →₀ ℕ) := Finsupp.equivMapDomain e.toEquiv ⁻¹' D
  have hD₀_up : IsUpperSet D₀ := fun α β hle hα ↦
    hD_up (fun j ↦ by obtain ⟨i, rfl⟩ := e.surjective j; simpa using hle i) hα
  have hD₀_mono : D₀.IsMonotoneDiagram :=
    (isMonotoneDiagram_preimage_equivMapDomain e).mpr hD_mono
  let H₀ : D₀.diagramVertices → MvPolynomial (Fin (Fintype.card σ)) A := fun v₀ ↦
    (renameEquiv A e.toEquiv).symm
      (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
        (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩)
  have hH₀ : ∀ v₀, (H₀ v₀).IsHomogeneous v₀.1.degree := fun v₀ ↦ by
    have hdeg : (Finsupp.equivMapDomain e.toEquiv v₀.1).degree = v₀.1.degree := by
      rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]
    have hh := hH ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
      (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩
    rw [hdeg] at hh
    exact (IsHomogeneous.rename_isHomogeneous_iff e.symm.injective).mpr
      (by simpa [H₀, renameEquiv_symm, renameEquiv_apply] using hh)
  have hk₀ : D₀.diagramCutoff ≤ k := by rwa [diagramCutoff_preimage_equivMapDomain e D]
  exact (homogeneousSubmodule_le_span_preimage_equivMapDomain_iff e D H ℓ).mp
    (homogeneousSubmodule_le_span_fin hD₀_up hD₀_mono hH₀ hk₀
      ((homogeneousSubmodule_le_span_preimage_equivMapDomain_iff e D H k).mpr hspan) hℓ)

/-- **Bierstone–Milman's Finite-Degree Criterion** (Theorem 8.1): for an upward-closed monotone
diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ` and homogeneous
polynomials `H v` of degree `v.1.degree` over a commutative ring `A`, if
`Submodule.span A (D.diagramSpanSet H k) = homogeneousSubmodule σ A k` at some
`k ≥ D.diagramCutoff`, then `Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ`
for every `ℓ ≥ k`. -/
theorem span_diagramSpanSet_eq_of_le {σ : Type*} [Finite σ] [LinearOrder σ]
    {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {k : ℕ} (hk : D.diagramCutoff ≤ k)
    (hspan : Submodule.span A (D.diagramSpanSet H k) = homogeneousSubmodule σ A k)
    {ℓ : ℕ} (hℓ : k ≤ ℓ) :
    Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule hH ℓ)
    (homogeneousSubmodule_le_span_diagramSpanSet_of_le hD_up hD_mono hH hk hspan.ge hℓ)

end FiniteDegreeCriterion

section HomogeneousDivisionBlocks

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommRing A]

private instance finiteDegreeEqSubtype (ℓ : ℕ) : Finite {δ : σ →₀ ℕ // δ.degree = ℓ} :=
  Finsupp.finite_of_degree_eq ℓ

private noncomputable instance fintypeDegreeEqSubtype (ℓ : ℕ) :
    Fintype {δ : σ →₀ ℕ // δ.degree = ℓ} :=
  Fintype.ofFinite _

open scoped Classical in
/-- The `A`-linear endomorphism of `homogeneousSubmodule σ A ℓ` associated to `D` and `H`, sending
`monomial δ 1` to `monomial (δ - v.1) 1 * H v` when `δ ∈ D.diagramCell v.1` and fixing
`monomial δ 1` outside all vertex cells. -/
noncomputable def diagramDivisionEnd (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    (ℓ : ℕ) :
    homogeneousSubmodule σ A ℓ →ₗ[A] homogeneousSubmodule σ A ℓ :=
  (TauCeti.homogeneousMonomialBasis ℓ).constr A fun s ↦
    if h : ∃ v : D.diagramVertices, s.1 ∈ D.diagramCell v.1 then
      ⟨monomial (s.1 - h.choose.1) 1 * H h.choose, by
        have hle : h.choose.1 ≤ s.1 := (D.mem_diagramCell_iff.mp h.choose_spec).1
        have hdeg : (s.1 - h.choose.1).degree + h.choose.1.degree = ℓ := by
          rw [← map_add, tsub_add_cancel_of_le hle, s.2]
        have hhom : (monomial (s.1 - h.choose.1) (1 : A) * H h.choose).IsHomogeneous
            ((s.1 - h.choose.1).degree + h.choose.1.degree) :=
          (isHomogeneous_monomial 1 (by simp [Finsupp.degree_apply])).mul (hH h.choose)
        rw [hdeg] at hhom
        exact (mem_homogeneousSubmodule ℓ _).mpr hhom⟩
    else
      TauCeti.homogeneousMonomialBasis ℓ s

theorem coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) {ℓ : ℕ}
    (v : D.diagramVertices) {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : s.1 ∈ D.diagramCell v.1) :
    (D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ s) : MvPolynomial σ A) =
      monomial (s.1 - v.1) 1 * H v := by
  classical
  have hex : ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := ⟨v, hs⟩
  have hchoose : hex.choose = v := by
    apply Subtype.ext
    by_contra hne
    exact (disjoint_diagramCell hex.choose.2 v.2 hne).le_bot ⟨hex.choose_spec, hs⟩
  simp only [diagramDivisionEnd, Module.Basis.constr_basis, hex, ↓reduceDIte, hchoose]

theorem diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) {ℓ : ℕ}
    {s : {δ : σ →₀ ℕ // δ.degree = ℓ}} (hs : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1) :
    D.diagramDivisionEnd H hH ℓ (TauCeti.homogeneousMonomialBasis ℓ s) =
      TauCeti.homogeneousMonomialBasis ℓ s := by
  classical
  have hex : ¬ ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := fun ⟨w, hw⟩ ↦ hs w hw
  simp only [diagramDivisionEnd, Module.Basis.constr_basis, hex, ↓reduceDIte]

/-- For an upward-closed diagram `D`, the image of `D.diagramDivisionEnd H hH ℓ` inside
`MvPolynomial σ A` is `Submodule.span A (D.diagramSpanSet H ℓ)`. -/
theorem map_range_diagramDivisionEnd_eq_span {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    (ℓ : ℕ) :
    (LinearMap.range (D.diagramDivisionEnd H hH ℓ)).map (homogeneousSubmodule σ A ℓ).subtype =
      Submodule.span A (D.diagramSpanSet H ℓ) := by
  let b := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  have hset : (fun s ↦ (D.diagramDivisionEnd H hH ℓ (b s) : MvPolynomial σ A)) '' Set.univ =
      D.diagramSpanSet H ℓ := by
    ext p
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨s, rfl⟩
      by_cases hsD : s.1 ∈ D
      · obtain ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hsD
        rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v hv]
        refine monomial_mul_mem_diagramSpanSet v (tsub_mem_diagramBox_of_mem_diagramCell hv) ?_
        rw [← map_add, add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hv).1, s.2]
      · have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦
          hsD (hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2))
        rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
          TauCeti.coe_homogeneousMonomialBasis]
        exact monomial_mem_diagramSpanSet hsD s.2
    · rintro (⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
      · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨v.1 + β, by rw [map_add, hdeg]⟩
        have hs : s.1 ∈ D.diagramCell v.1 := add_mem_diagramCell_iff.mpr hβ
        refine ⟨s, ?_⟩
        rw [coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v hs]
        simp [s]
      · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨γ, hdeg⟩
        have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦
          hγ (hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2))
        refine ⟨s, ?_⟩
        rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
          TauCeti.coe_homogeneousMonomialBasis]
  rw [← hset]
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [← b.sum_repr x, map_sum, map_sum]
    refine Submodule.sum_mem _ fun s _ ↦ ?_
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, trivial, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, _, rfl⟩
    exact ⟨D.diagramDivisionEnd H hH ℓ (b s), ⟨b s, rfl⟩, rfl⟩

theorem surjective_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    Function.Surjective (D.diagramDivisionEnd H hH ℓ) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← LinearMap.range_eq_top, ← map_range_diagramDivisionEnd_eq_span hD_up hH ℓ]
  refine ⟨fun h ↦ by rw [h, Submodule.map_top, Submodule.range_subtype], fun h ↦ ?_⟩
  rw [eq_top_iff]
  intro y _
  have hy : (y : MvPolynomial σ A) ∈
      (LinearMap.range (D.diagramDivisionEnd H hH ℓ)).map (homogeneousSubmodule σ A ℓ).subtype := by
    rw [h]
    exact y.2
  obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
  exact Subtype.ext hzy ▸ hz

theorem bijective_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    Function.Bijective (D.diagramDivisionEnd H hH ℓ) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  ⟨fun h ↦ (surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mp h.2,
    fun h ↦ OrzechProperty.bijective_of_surjective_endomorphism _
      ((surjective_diagramDivisionEnd_iff_span_eq hD_up hH).mpr h)⟩

theorem isUnit_det_diagramDivisionEnd_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    IsUnit (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff,
    bijective_diagramDivisionEnd_iff_span_eq hD_up hH]

private theorem eq_sum_diagramCell_of_mem_restrictSupport {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    {v : D.diagramVertices} {q : MvPolynomial σ A}
    (hq : q ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ})
    [DecidablePred fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D.diagramCell v.1] :
    q = ∑ s ∈ Finset.univ.filter
        (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D.diagramCell v.1),
        monomial (s.1 - v.1) (q.coeff (s.1 - v.1)) := by
  ext β
  rw [coeff_sum]
  by_cases hβ : β ∈ {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ}
  · let s₀ : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨v.1 + β, by rw [map_add, hβ.2]⟩
    have hs₀ : s₀ ∈ Finset.univ.filter
        (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D.diagramCell v.1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ s₀, add_mem_diagramCell_iff.mpr hβ.1⟩
    rw [Finset.sum_eq_single s₀]
    · simp [s₀]
    · intro s hs hne
      have hsc : s.1 ∈ D.diagramCell v.1 := (Finset.mem_filter.mp hs).2
      have hne' : s.1 - v.1 ≠ β := fun heq ↦ hne (Subtype.ext <| by
        simp only [s₀]
        rw [← heq, add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hsc).1])
      simp [coeff_monomial, hne']
    · intro habs
      exact absurd hs₀ habs
  · have hzero : q.coeff β = 0 := by
      by_contra hne
      exact hβ ((mem_restrictSupport_iff A).mp hq (mem_support_iff.mpr hne))
    rw [hzero]
    symm
    refine Finset.sum_eq_zero fun s hs ↦ ?_
    have hsc : s.1 ∈ D.diagramCell v.1 := (Finset.mem_filter.mp hs).2
    have hmem : s.1 - v.1 ∈ {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ} :=
      ⟨tsub_mem_diagramBox_of_mem_diagramCell hsc, by
        rw [← map_add, add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hsc).1, s.2]⟩
    have hne' : s.1 - v.1 ≠ β := fun heq ↦ hβ (heq ▸ hmem)
    simp [coeff_monomial, hne']

private theorem eq_sum_compl_of_mem_restrictSupport {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    {R : MvPolynomial σ A} (hR : R ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ})
    [DecidablePred fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ ¬ s.1 ∈ D] :
    R = ∑ s ∈ Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ ¬ s.1 ∈ D),
        monomial s.1 (R.coeff s.1) := by
  ext γ
  rw [coeff_sum]
  by_cases hγ : γ ∉ D ∧ γ.degree = ℓ
  · let s₀ : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨γ, hγ.2⟩
    have hs₀ : s₀ ∈ Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ ¬ s.1 ∈ D) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ s₀, hγ.1⟩
    rw [Finset.sum_eq_single s₀]
    · simp [s₀]
    · intro s _ hne
      have hne' : s.1 ≠ γ := Subtype.coe_ne_coe.mpr hne
      simp [coeff_monomial, hne']
    · intro habs
      exact absurd hs₀ habs
  · have hzero : R.coeff γ = 0 := by
      by_contra hne
      exact hγ ((mem_restrictSupport_iff A).mp hR (mem_support_iff.mpr hne))
    rw [hzero]
    symm
    refine Finset.sum_eq_zero fun s hs ↦ ?_
    have hs' : s.1 ∉ D ∧ s.1.degree = ℓ := ⟨(Finset.mem_filter.mp hs).2, s.2⟩
    have hne' : s.1 ≠ γ := fun heq ↦ hγ (heq ▸ hs')
    simp [coeff_monomial, hne']

/-- Expand `(D.diagramDivisionEnd H hH ℓ P : MvPolynomial σ A)` into supported quotients and
remainder. -/
private theorem coe_diagramDivisionEnd_eq_sum_add {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} {Q : D.diagramVertices → MvPolynomial σ A} {R : MvPolynomial σ A}
    (hQ : ∀ v, Q v ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ})
    (hR : R ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ})
    {P : homogeneousSubmodule σ A ℓ}
    (hP_cell : ∀ (v : D.diagramVertices) (s : {δ : σ →₀ ℕ // δ.degree = ℓ}),
      s.1 ∈ D.diagramCell v.1 → P.1.coeff s.1 = (Q v).coeff (s.1 - v.1))
    (hP_rem : ∀ s : {δ : σ →₀ ℕ // δ.degree = ℓ}, s.1 ∉ D → P.1.coeff s.1 = R.coeff s.1) :
    (D.diagramDivisionEnd H hH ℓ P : MvPolynomial σ A) = ∑ v, Q v * H v + R := by
  classical
  conv_lhs =>
    rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P,
      map_sum, Submodule.coe_sum]
  simp_rw [map_smul, SetLike.val_smul, TauCeti.homogeneousMonomialBasis_repr_apply]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦
    s.1 ∈ D)]
  congr 1
  · have hpart : Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D) =
        Finset.univ.biUnion (fun v : D.diagramVertices ↦
          Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦
            s.1 ∈ D.diagramCell v.1)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun hs ↦ let ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hs; ⟨v, hv⟩,
        fun ⟨v, hv⟩ ↦ hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2)⟩
    rw [hpart, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun v _ ↦ ?_
      conv_rhs => rw [eq_sum_diagramCell_of_mem_restrictSupport (hQ v), Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      have hsc : s.1 ∈ D.diagramCell v.1 := (Finset.mem_filter.mp hs).2
      rw [hP_cell v s hsc,
        coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v hsc,
        ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
    · intro v₁ _ v₂ _ hne
      refine Finset.disjoint_left.mpr fun s hs₁ hs₂ ↦ ?_
      exact (disjoint_diagramCell v₁.2 v₂.2 (Subtype.coe_ne_coe.mpr hne)).le_bot
        ⟨(Finset.mem_filter.mp hs₁).2, (Finset.mem_filter.mp hs₂).2⟩
  · conv_rhs => rw [eq_sum_compl_of_mem_restrictSupport hR]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    have hsD : s.1 ∉ D := (Finset.mem_filter.mp hs).2
    have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦
      hsD (hD_up (D.mem_diagramCell_iff.mp hv).1 (D.diagramVertices_subset v.2))
    rw [hP_rem s hsD, diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
      TauCeti.coe_homogeneousMonomialBasis, smul_monomial, smul_eq_mul, mul_one]

open scoped Classical in
/-- Split a homogeneous polynomial `P` of degree `ℓ` into supported quotients `Q v` and a
complementary remainder `R`. -/
private noncomputable def diagramToQR (D : Set (σ →₀ ℕ)) {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A :=
  (fun v ↦ ∑ s ∈ Finset.univ.filter
      (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∈ D.diagramCell v.1),
      monomial (s.1 - v.1) (P.1.coeff s.1),
    ∑ s ∈ Finset.univ.filter (fun s : {δ : σ →₀ ℕ // δ.degree = ℓ} ↦ s.1 ∉ D),
      monomial s.1 (P.1.coeff s.1))

private theorem diagramToQR_fst_mem {D : Set (σ →₀ ℕ)} {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ)
    (v : D.diagramVertices) :
    (D.diagramToQR P).1 v ∈
      restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ} := by
  classical
  rw [diagramToQR]
  refine Submodule.sum_mem _ fun s hs ↦ ?_
  have hsc : s.1 ∈ D.diagramCell v.1 := (Finset.mem_filter.mp hs).2
  rw [mem_restrictSupport_iff]
  intro β hβ
  rw [Finset.mem_coe] at hβ
  rcases Finset.mem_singleton.mp (support_monomial_subset hβ) with rfl
  exact ⟨tsub_mem_diagramBox_of_mem_diagramCell hsc, by
    rw [← map_add, add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hsc).1, s.2]⟩

private theorem diagramToQR_snd_mem {D : Set (σ →₀ ℕ)} {ℓ : ℕ} (P : homogeneousSubmodule σ A ℓ) :
    (D.diagramToQR P).2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} := by
  classical
  rw [diagramToQR]
  refine Submodule.sum_mem _ fun s hs ↦ ?_
  have hsD : s.1 ∉ D := (Finset.mem_filter.mp hs).2
  rw [mem_restrictSupport_iff]
  intro γ hγ
  rw [Finset.mem_coe] at hγ
  rcases Finset.mem_singleton.mp (support_monomial_subset hγ) with rfl
  exact ⟨hsD, s.2⟩

private theorem diagramToQR_coeff_cell {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (v : D.diagramVertices)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.1 ∈ D.diagramCell v.1) :
    P.1.coeff s.1 = ((D.diagramToQR P).1 v).coeff (s.1 - v.1) := by
  classical
  rw [diagramToQR]
  simp only [coeff_sum]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' hs' hne
    have hs'c : s'.1 ∈ D.diagramCell v.1 := (Finset.mem_filter.mp hs').2
    have hne' : s'.1 - v.1 ≠ s.1 - v.1 := fun heq ↦ hne (Subtype.ext <| by
      rw [← add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hs'c).1, heq,
        add_tsub_cancel_of_le (D.mem_diagramCell_iff.mp hs).1])
    simp [coeff_monomial, hne']
  · intro habs
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩) habs

private theorem diagramToQR_coeff_rem {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (P : homogeneousSubmodule σ A ℓ) (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.1 ∉ D) :
    P.1.coeff s.1 = (D.diagramToQR P).2.coeff s.1 := by
  classical
  rw [diagramToQR]
  simp only [coeff_sum]
  rw [Finset.sum_eq_single s]
  · simp
  · intro s' _ hne
    have hne' : s'.1 ≠ s.1 := Subtype.coe_ne_coe.mpr hne
    simp [coeff_monomial, hne']
  · intro habs
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩) habs

open scoped Classical in
/-- Reassemble a degree-`ℓ` homogeneous polynomial from quotients `qr.1` and remainder `qr.2`. -/
private noncomputable def diagramFromQR (D : Set (σ →₀ ℕ)) (ℓ : ℕ)
    (qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A) :
    homogeneousSubmodule σ A ℓ :=
  (TauCeti.homogeneousMonomialBasis ℓ).repr.symm (Finsupp.equivFunOnFinite.symm fun s ↦
    if h : ∃ v : D.diagramVertices, s.1 ∈ D.diagramCell v.1 then
      (qr.1 h.choose).coeff (s.1 - h.choose.1)
    else qr.2.coeff s.1)

private theorem diagramFromQR_coeff_cell {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A)
    (v : D.diagramVertices) (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.1 ∈ D.diagramCell v.1) :
    (D.diagramFromQR ℓ qr).1.coeff s.1 = (qr.1 v).coeff (s.1 - v.1) := by
  classical
  have hex : ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := ⟨v, hs⟩
  have hchoose : hex.choose = v := by
    apply Subtype.ext
    by_contra hne
    exact (disjoint_diagramCell hex.choose.2 v.2 hne).le_bot ⟨hex.choose_spec, hs⟩
  rw [← TauCeti.homogeneousMonomialBasis_repr_apply ℓ (D.diagramFromQR ℓ qr) s, diagramFromQR,
    LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
  simp only [hex, ↓reduceDIte, hchoose]

private theorem diagramFromQR_coeff_rem {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    (qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A)
    (s : {δ : σ →₀ ℕ // δ.degree = ℓ}) (hs : s.1 ∉ D) :
    (D.diagramFromQR ℓ qr).1.coeff s.1 = qr.2.coeff s.1 := by
  classical
  have hex : ¬ ∃ w : D.diagramVertices, s.1 ∈ D.diagramCell w.1 := fun ⟨w, hw⟩ ↦
    hs (hD_up (D.mem_diagramCell_iff.mp hw).1 (D.diagramVertices_subset w.2))
  rw [← TauCeti.homogeneousMonomialBasis_repr_apply ℓ (D.diagramFromQR ℓ qr) s, diagramFromQR,
    LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
  simp only [hex, ↓reduceDIte]

private theorem diagramToQR_injective {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    {P₁ P₂ : homogeneousSubmodule σ A ℓ} (heq : D.diagramToQR P₁ = D.diagramToQR P₂) :
    P₁ = P₂ := by
  refine (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).repr.injective
    (Finsupp.ext fun s ↦ ?_)
  rw [TauCeti.homogeneousMonomialBasis_repr_apply, TauCeti.homogeneousMonomialBasis_repr_apply]
  by_cases hsD : s.1 ∈ D
  · obtain ⟨v, hv, _⟩ := existsUnique_mem_diagramCell_of_mem hD_up hsD
    rw [diagramToQR_coeff_cell P₁ v s hv, diagramToQR_coeff_cell P₂ v s hv, heq]
  · rw [diagramToQR_coeff_rem P₁ s hsD, diagramToQR_coeff_rem P₂ s hsD, heq]

private theorem diagramToQR_diagramFromQR {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) {ℓ : ℕ}
    {qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A}
    (hQ : ∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ})
    (hR : qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ}) :
    D.diagramToQR (D.diagramFromQR ℓ qr) = qr := by
  refine Prod.ext (funext fun v ↦ (eq_of_mem_restrictSupport_of_coeff_eq (hQ v)
    (diagramToQR_fst_mem (D.diagramFromQR ℓ qr) v) fun β hβ ↦ ?_).symm)
    (eq_of_mem_restrictSupport_of_coeff_eq hR (diagramToQR_snd_mem (D.diagramFromQR ℓ qr))
      fun γ hγ ↦ ?_).symm
  · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨v.1 + β, by rw [map_add, hβ.2]⟩
    have hs : s.1 ∈ D.diagramCell v.1 := add_mem_diagramCell_iff.mpr hβ.1
    have h₁ := diagramFromQR_coeff_cell qr v s hs
    have h₂ := diagramToQR_coeff_cell (D.diagramFromQR ℓ qr) v s hs
    simp only [s, add_tsub_cancel_left] at h₁ h₂
    exact h₁.symm.trans h₂
  · let s : {δ : σ →₀ ℕ // δ.degree = ℓ} := ⟨γ, hγ.2⟩
    exact (diagramFromQR_coeff_rem hD_up qr s hγ.1).symm.trans
      (diagramToQR_coeff_rem (D.diagramFromQR ℓ qr) s hγ.1)

/-- Spanning in degree `ℓ` is equivalent to unique homogeneous supported division in degree `ℓ`. -/
theorem existsUnique_homogeneous_division_iff_span_eq {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    {ℓ : ℕ} :
    (∀ G ∈ homogeneousSubmodule σ A ℓ,
      ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
        (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ}) ∧
        qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
        ∑ v, qr.1 v * H v + qr.2 = G) ↔
      Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [← bijective_diagramDivisionEnd_iff_span_eq hD_up hH]
  constructor
  · intro hdiv
    refine ⟨fun P₁ P₂ hP ↦ diagramToQR_injective hD_up ?_, fun G ↦ ?_⟩
    · obtain ⟨_, _, huniq⟩ := hdiv (D.diagramDivisionEnd H hH ℓ P₁)
        (D.diagramDivisionEnd H hH ℓ P₁).2
      have h₁ := (coe_diagramDivisionEnd_eq_sum_add hD_up hH (diagramToQR_fst_mem P₁)
        (diagramToQR_snd_mem P₁) (diagramToQR_coeff_cell P₁) (diagramToQR_coeff_rem P₁)).symm
      have h₂ : ∑ v, (D.diagramToQR P₂).1 v * H v + (D.diagramToQR P₂).2 =
          (D.diagramDivisionEnd H hH ℓ P₁ : MvPolynomial σ A) := by
        rw [hP]
        exact (coe_diagramDivisionEnd_eq_sum_add hD_up hH (diagramToQR_fst_mem P₂)
          (diagramToQR_snd_mem P₂) (diagramToQR_coeff_cell P₂) (diagramToQR_coeff_rem P₂)).symm
      exact (huniq _ ⟨diagramToQR_fst_mem P₁, diagramToQR_snd_mem P₁, h₁⟩).trans
        (huniq _ ⟨diagramToQR_fst_mem P₂, diagramToQR_snd_mem P₂, h₂⟩).symm
    · obtain ⟨qr, ⟨hQ, hR, hsum⟩, _⟩ := hdiv G.1 G.2
      refine ⟨D.diagramFromQR ℓ qr, Subtype.ext ?_⟩
      rw [coe_diagramDivisionEnd_eq_sum_add hD_up hH hQ hR (diagramFromQR_coeff_cell qr)
        (diagramFromQR_coeff_rem hD_up qr), hsum]
  · intro hbij G hG
    obtain ⟨P, hP⟩ := hbij.2 ⟨G, hG⟩
    refine ⟨D.diagramToQR P, ⟨diagramToQR_fst_mem P, diagramToQR_snd_mem P, ?_⟩,
      fun qr ⟨hQ, hR, hsum⟩ ↦ ?_⟩
    · rw [← coe_diagramDivisionEnd_eq_sum_add hD_up hH (diagramToQR_fst_mem P)
        (diagramToQR_snd_mem P) (diagramToQR_coeff_cell P) (diagramToQR_coeff_rem P), hP]
    · have hend : D.diagramDivisionEnd H hH ℓ (D.diagramFromQR ℓ qr) = ⟨G, hG⟩ := Subtype.ext <| by
        rw [coe_diagramDivisionEnd_eq_sum_add hD_up hH hQ hR (diagramFromQR_coeff_cell qr)
          (diagramFromQR_coeff_rem hD_up qr), hsum]
      exact (diagramToQR_diagramFromQR hD_up hQ hR).symm.trans
        (congrArg D.diagramToQR (hbij.1 (hend.trans hP.symm)))

/-- `diagramDivisionEnd` commutes with changing coefficients along any ring homomorphism
`φ : A →+* B`. -/
theorem mapHomogeneousSubmodule_diagramDivisionEnd {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) (ℓ : ℕ)
    (P : homogeneousSubmodule σ A ℓ) :
    TauCeti.mapHomogeneousSubmodule φ ℓ (D.diagramDivisionEnd H hH ℓ P) =
      D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ
        (TauCeti.mapHomogeneousSubmodule φ ℓ P) := by
  rw [← (TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ).sum_repr P,
    map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [LinearMap.map_smulₛₗ, TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis]
  congr 1
  apply Subtype.ext
  classical
  by_cases hex : ∃ v : D.diagramVertices, s.1 ∈ D.diagramCell v.1
  · obtain ⟨v, hv⟩ := hex
    rw [TauCeti.coe_mapHomogeneousSubmodule_apply,
      coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell hH v hv,
      coe_diagramDivisionEnd_homogeneousMonomialBasis_of_mem_diagramCell _ v hv,
      map_mul, map_monomial, map_one]
  · have hnot : ∀ v : D.diagramVertices, s.1 ∉ D.diagramCell v.1 := fun v hv ↦ hex ⟨v, hv⟩
    rw [diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell hH hnot,
      diagramDivisionEnd_homogeneousMonomialBasis_of_notMem_diagramCell _ hnot,
      TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis]

/-- Changing coefficients along `φ : A →+* B` maps the block determinant of
`D.diagramDivisionEnd H hH ℓ` to the block determinant of `MvPolynomial.map φ ∘ H`. -/
theorem map_det_diagramDivisionEnd {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) (ℓ : ℕ) :
    φ (LinearMap.det (D.diagramDivisionEnd H hH ℓ)) =
      LinearMap.det
        (D.diagramDivisionEnd (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) ℓ) := by
  classical
  let bA := TauCeti.homogeneousMonomialBasis (σ := σ) (R := A) ℓ
  let bB := TauCeti.homogeneousMonomialBasis (σ := σ) (R := B) ℓ
  rw [← LinearMap.det_toMatrix bA, ← LinearMap.det_toMatrix bB, RingHom.map_det]
  congr 1
  ext s t
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, TauCeti.homogeneousMonomialBasis_repr_apply,
    TauCeti.homogeneousMonomialBasis_repr_apply]
  have hcomm := mapHomogeneousSubmodule_diagramDivisionEnd φ hH ℓ (bA t)
  rw [TauCeti.mapHomogeneousSubmodule_homogeneousMonomialBasis] at hcomm
  have hval := congrArg (fun x : homogeneousSubmodule σ B ℓ ↦ x.1.coeff s.1) hcomm
  simpa [TauCeti.coe_mapHomogeneousSubmodule_apply, coeff_map] using hval

/-- The finite-jet determinant product across degrees `ℓ ≤ D.diagramCutoff` controlling
homogeneous supported division in *all* degrees for a monotone upward-closed diagram `D`
(Bierstone–Milman, p. 282). -/
noncomputable def diagramCutoffDet (D : Set (σ →₀ ℕ))
    (H : D.diagramVertices → MvPolynomial σ A) (hH : ∀ v, (H v).IsHomogeneous v.1.degree) : A :=
  ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ)

theorem diagramCutoffDet_def (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A)
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    D.diagramCutoffDet H hH =
      ∏ ℓ ∈ Finset.range (D.diagramCutoff + 1), LinearMap.det (D.diagramDivisionEnd H hH ℓ) :=
  (rfl)

theorem map_diagramCutoffDet {B : Type*} [CommRing B] (φ : A →+* B)
    {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    φ (D.diagramCutoffDet H hH) =
      D.diagramCutoffDet (fun v ↦ MvPolynomial.map φ (H v)) (fun v ↦ (hH v).map φ) := by
  simp [diagramCutoffDet_def, map_prod, map_det_diagramDivisionEnd]

/-- For an upward-closed monotone diagram `D`, the single finite-jet determinant product
`D.diagramCutoffDet H hH` is a unit in `A` if and only if `D.diagramSpanSet H ℓ` spans
`homogeneousSubmodule σ A ℓ` in *every* degree `ℓ : ℕ`. -/
theorem isUnit_diagramCutoffDet_iff_forall_span_eq {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ : ℕ, Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [diagramCutoffDet_def, IsUnit.prod_iff]
  refine ⟨fun h ℓ ↦ ?_, fun h ℓ _ ↦ (isUnit_det_diagramDivisionEnd_iff_span_eq hD_up hH).mpr (h ℓ)⟩
  by_cases hle : ℓ ≤ D.diagramCutoff
  · exact (isUnit_det_diagramDivisionEnd_iff_span_eq hD_up hH).mp
      (h ℓ (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
  · have hcut : Submodule.span A (D.diagramSpanSet H D.diagramCutoff) =
        homogeneousSubmodule σ A D.diagramCutoff :=
      (isUnit_det_diagramDivisionEnd_iff_span_eq hD_up hH).mp
        (h D.diagramCutoff (Finset.mem_range.mpr (Nat.lt_succ_self _)))
    exact span_diagramSpanSet_eq_of_le hD_up hD_mono hH le_rfl hcut (Nat.le_of_not_ge hle)

/-- For an upward-closed monotone diagram `D`, `D.diagramCutoffDet H hH` is a unit in `A` if and
only if unique homogeneous supported division holds in *every* degree `ℓ : ℕ`. -/
theorem isUnit_diagramCutoffDet_iff_forall_existsUnique_division {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    IsUnit (D.diagramCutoffDet H hH) ↔
      ∀ ℓ : ℕ, ∀ G ∈ homogeneousSubmodule σ A ℓ,
        ∃! qr : (D.diagramVertices → MvPolynomial σ A) × MvPolynomial σ A,
          (∀ v, qr.1 v ∈ restrictSupport A {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ}) ∧
          qr.2 ∈ restrictSupport A {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
          ∑ v, qr.1 v * H v + qr.2 = G := by
  rw [isUnit_diagramCutoffDet_iff_forall_span_eq hD_up hD_mono hH]
  exact forall_congr' fun ℓ ↦ (existsUnique_homogeneous_division_iff_span_eq hD_up hH).symm

/-- After any ring homomorphism `φ : A →+* B` (such as `algebraMap A (Localization.Away _)`) that
inverts `D.diagramCutoffDet H hH`, unique homogeneous supported division for
`MvPolynomial.map φ ∘ H` holds in *every* degree `ℓ : ℕ` (Bierstone–Milman, p. 282). -/
theorem existsUnique_homogeneous_division_of_isUnit_map_diagramCutoffDet
    {B : Type*} [CommRing B] (φ : A →+* B) {D : Set (σ →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.1.degree)
    (hunit : IsUnit (φ (D.diagramCutoffDet H hH))) (ℓ : ℕ)
    {G : MvPolynomial σ B} (hG : G ∈ homogeneousSubmodule σ B ℓ) :
    ∃! qr : (D.diagramVertices → MvPolynomial σ B) × MvPolynomial σ B,
      (∀ v, qr.1 v ∈ restrictSupport B {β ∈ D.diagramBox v.1 | v.1.degree + β.degree = ℓ}) ∧
      qr.2 ∈ restrictSupport B {γ | γ ∉ D ∧ γ.degree = ℓ} ∧
      ∑ v, qr.1 v * MvPolynomial.map φ (H v) + qr.2 = G := by
  rw [map_diagramCutoffDet] at hunit
  exact (isUnit_diagramCutoffDet_iff_forall_existsUnique_division hD_up hD_mono
    (fun v ↦ (hH v).map φ)).mp hunit ℓ G hG

end HomogeneousDivisionBlocks

section ChecksAndSharpness

section BoundaryCases

variable {σ A : Type*} [Finite σ] [LinearOrder σ] [CommSemiring A]

/-- For `D = Set.univ` (the quadrant of the vertex `0`), spanning in degree `0` holds if and only
if the constant polynomial `H ⟨0, _⟩` is a unit in `A`. -/
theorem span_diagramSpanSet_univ_zero_iff
    {H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    Submodule.span A ((Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H 0) =
        homogeneousSubmodule σ A 0 ↔
      IsUnit (constantCoeff (H ⟨0, by simp⟩)) := by
  let v₀ : (Set.univ : Set (σ →₀ ℕ)).diagramVertices := ⟨0, by simp⟩
  have hv₀_eq : H v₀ = C (constantCoeff (H v₀)) := by
    have h0 : (H v₀).IsHomogeneous 0 := by simpa [v₀] using hH v₀
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h0
    conv_lhs => rw [h0]
    conv_rhs => rw [h0, constantCoeff_C]
  have hset : (Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H 0 = {H v₀} := by
    ext p
    simp only [mem_diagramSpanSet_iff, mem_univ, not_true_eq_false, false_and, exists_false,
      or_false, mem_singleton_iff]
    constructor
    · rintro ⟨⟨v, hv⟩, β, _, hdeg, rfl⟩
      have hv_zero : v = 0 := by simpa using hv
      subst hv_zero
      have hβ_zero : β = 0 := by
        rw [← Finsupp.degree_eq_zero_iff]
        simpa using hdeg
      subst hβ_zero
      simp [v₀]
    · rintro rfl
      exact ⟨v₀, 0, by simp [v₀], by simp [v₀], by simp⟩
  rw [hset, hv₀_eq, isUnit_iff_exists_inv']
  constructor
  · intro hspan
    have h1 : (1 : MvPolynomial σ A) ∈ Submodule.span A {C (constantCoeff (H v₀))} := by
      rw [hspan, mem_homogeneousSubmodule]
      exact isHomogeneous_one σ A
    rw [Submodule.mem_span_singleton] at h1
    obtain ⟨a, ha⟩ := h1
    refine ⟨a, ?_⟩
    simpa [smul_eq_C_mul] using congrArg constantCoeff ha
  · rintro ⟨a, ha⟩
    apply le_antisymm
    · rw [← hv₀_eq, ← hset]
      exact span_diagramSpanSet_le_homogeneousSubmodule hH 0
    · intro p hp
      have hp0 : p.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 p).mp hp
      rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp0
      rw [hp0, Submodule.mem_span_singleton]
      rw [constantCoeff_C] at ha
      refine ⟨p.coeff 0 * a, ?_⟩
      rw [smul_eq_C_mul, ← map_mul, mul_assoc, ha, mul_one]

/-- For `D = Set.univ`, `D.diagramSpanSet H ℓ` spans in *all* degrees `ℓ : ℕ` if and only if
`constantCoeff (H ⟨0, _⟩)` is a unit in `A`. -/
theorem forall_span_diagramSpanSet_univ_iff {R : Type*} [CommRing R]
    {H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ R}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    (∀ ℓ : ℕ, Submodule.span R ((Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ) =
        homogeneousSubmodule σ R ℓ) ↔
      IsUnit (constantCoeff (H ⟨0, by simp⟩)) :=
  ⟨fun h ↦ (span_diagramSpanSet_univ_zero_iff hH).mp (h 0), fun h ℓ ↦
    span_diagramSpanSet_eq_of_le isUpperSet_univ isMonotoneDiagram_univ hH
      (by simp) ((span_diagramSpanSet_univ_zero_iff hH).mpr h) (Nat.zero_le ℓ)⟩

private theorem eq_single_zero_of_fin_one (γ : Fin 1 →₀ ℕ) :
    γ = Finsupp.single 0 γ.degree := by
  refine Finsupp.ext fun i ↦ ?_
  rw [Subsingleton.elim i 0, Finsupp.degree_eq_sum, Fintype.sum_unique, Fin.default_eq_zero,
    Finsupp.single_eq_same]

/-- In one variable (`Fin 1`), for the cone `D = Set.Ici (Finsupp.single 0 a)` and `ℓ < a`, the
complementary monomial `X 0 ^ ℓ` spans `homogeneousSubmodule (Fin 1) A ℓ` unconditionally. -/
theorem span_diagramSpanSet_Ici_single_fin_one_of_lt {a ℓ : ℕ} (hℓ : ℓ < a)
    (H : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices → MvPolynomial (Fin 1) A)
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    Submodule.span A ((Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramSpanSet H ℓ) =
      homogeneousSubmodule (Fin 1) A ℓ := by
  apply le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule hH ℓ)
  intro p hp
  have hp_hom : p.IsHomogeneous ℓ := (mem_homogeneousSubmodule ℓ p).mp hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun γ hγ ↦ ?_
  have hdeg : γ.degree = ℓ := by
    rw [Finsupp.degree_apply]
    exact (hp_hom.degree_eq_sum_deg_support hγ).symm
  have hγ_eq : γ = Finsupp.single 0 ℓ := hdeg ▸ eq_single_zero_of_fin_one γ
  have hnot : γ ∉ Set.Ici (Finsupp.single (0 : Fin 1) a) := by
    rw [hγ_eq, mem_Ici, Finsupp.single_le_iff, Finsupp.single_eq_same]
    omega
  have hsmul : p.coeff γ • monomial γ (1 : A) = monomial γ (p.coeff γ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [← hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (monomial_mem_diagramSpanSet hnot hdeg))

/-- In one variable (`Fin 1`), for the cone `D = Set.Ici (Finsupp.single 0 a)` and `a ≤ ℓ`,
`D.diagramSpanSet H ℓ` spans `homogeneousSubmodule (Fin 1) A ℓ` if and only if the coefficient of
`X 0 ^ a` in `H ⟨Finsupp.single 0 a, _⟩` is a unit in `A`. -/
private theorem diagramSpanSet_Ici_single_fin_one_eq {a ℓ : ℕ} (haℓ : a ≤ ℓ)
    {H : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices → MvPolynomial (Fin 1) A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramSpanSet H ℓ =
      {monomial (Finsupp.single 0 ℓ)
        ((H ⟨Finsupp.single 0 a, by simp⟩).coeff (Finsupp.single 0 a))} := by
  let v₀ : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices :=
    ⟨Finsupp.single 0 a, by simp⟩
  have hv₀_eq : H v₀ = monomial (Finsupp.single 0 a) ((H v₀).coeff (Finsupp.single 0 a)) := by
    ext γ
    by_cases hγ : γ = Finsupp.single 0 a
    · subst hγ; simp
    · simp only [coeff_monomial, Ne.symm hγ, ↓reduceIte]
      refine (hH v₀).coeff_eq_zero fun hd ↦ hγ ?_
      have hdeg_γ : γ.degree = v₀.1.degree := by rw [Finsupp.degree_apply]; exact hd
      rw [eq_single_zero_of_fin_one γ, hdeg_γ]
      simp [v₀]
  ext p
  simp only [mem_diagramSpanSet_iff, mem_singleton_iff]
  constructor
  · rintro (⟨⟨v, hv⟩, β, _, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
    · have hv_eq : v = Finsupp.single 0 a := by simpa using hv
      subst hv_eq
      have hβ_eq : β = Finsupp.single 0 (ℓ - a) := by
        rw [eq_single_zero_of_fin_one β]
        rw [Finsupp.degree_single] at hdeg
        congr 1; omega
      subst hβ_eq
      have hv_sub : (⟨Finsupp.single 0 a, hv⟩ :
          (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices) = v₀ := rfl
      conv_lhs => rw [hv_sub, hv₀_eq]
      rw [monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.sub_add_cancel haℓ]
    · exfalso
      exact hγ <| by
        rw [eq_single_zero_of_fin_one γ, hdeg, mem_Ici, Finsupp.single_le_iff,
          Finsupp.single_eq_same]
        exact haℓ
  · rintro rfl
    refine Or.inl ⟨v₀, Finsupp.single 0 (ℓ - a),
      mem_diagramBox_iff.mpr fun α' hα' hlt ↦ ?_, ?_, ?_⟩
    · have hα'_eq : α' = v₀.1 := by simpa [v₀] using hα'
      exact absurd (hα'_eq ▸ hlt) (lt_irrefl _)
    · have hv₀_val : v₀.1 = Finsupp.single 0 a := rfl
      rw [hv₀_val, Finsupp.degree_single, Finsupp.degree_single]
      omega
    · conv_rhs => rw [hv₀_eq]
      rw [monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.sub_add_cancel haℓ]

/-- In one variable (`Fin 1`), for the cone `D = Set.Ici (Finsupp.single 0 a)` and `a ≤ ℓ`,
`D.diagramSpanSet H ℓ` spans `homogeneousSubmodule (Fin 1) A ℓ` if and only if the coefficient of
`X 0 ^ a` in `H ⟨Finsupp.single 0 a, _⟩` is a unit in `A`. -/
theorem span_diagramSpanSet_Ici_single_fin_one_iff {a ℓ : ℕ} (haℓ : a ≤ ℓ)
    {H : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices → MvPolynomial (Fin 1) A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    Submodule.span A ((Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramSpanSet H ℓ) =
        homogeneousSubmodule (Fin 1) A ℓ ↔
      IsUnit ((H ⟨Finsupp.single 0 a, by simp⟩).coeff (Finsupp.single 0 a)) := by
  have hset := diagramSpanSet_Ici_single_fin_one_eq haℓ hH
  rw [hset, isUnit_iff_exists_inv']
  constructor
  · intro hspan
    have hm : monomial (Finsupp.single (0 : Fin 1) ℓ) (1 : A) ∈ Submodule.span A
        {monomial (Finsupp.single 0 ℓ)
          ((H ⟨Finsupp.single 0 a, by simp⟩).coeff (Finsupp.single 0 a))} := by
      rw [hspan, mem_homogeneousSubmodule]
      exact isHomogeneous_monomial 1 (Finsupp.degree_single 0 ℓ)
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨u, hu⟩ := hm
    refine ⟨u, ?_⟩
    simpa [smul_monomial] using
      congrArg (fun q : MvPolynomial (Fin 1) A ↦ q.coeff (Finsupp.single 0 ℓ)) hu
  · rintro ⟨u, hu⟩
    apply le_antisymm (hset ▸ span_diagramSpanSet_le_homogeneousSubmodule hH ℓ)
    intro p hp
    have hp_hom : p.IsHomogeneous ℓ := (mem_homogeneousSubmodule ℓ p).mp hp
    have hp_eq : p = monomial (Finsupp.single 0 ℓ) (p.coeff (Finsupp.single 0 ℓ)) := by
      ext γ
      by_cases hγ : γ = Finsupp.single 0 ℓ
      · subst hγ; simp
      · simp only [coeff_monomial, Ne.symm hγ, ↓reduceIte]
        refine hp_hom.coeff_eq_zero fun hd ↦ hγ ?_
        have hdeg_γ : γ.degree = ℓ := by rw [Finsupp.degree_apply]; exact hd
        rw [eq_single_zero_of_fin_one γ, hdeg_γ]
    rw [hp_eq, Submodule.mem_span_singleton]
    refine ⟨p.coeff (Finsupp.single 0 ℓ) * u, ?_⟩
    rw [smul_monomial, smul_eq_mul, mul_assoc, hu, mul_one]

end BoundaryCases

section CutoffSharpness

private def sharpDiagram : Set (Fin 2 →₀ ℕ) :=
  {γ | 2 ≤ γ 1 ∨ 3 ≤ γ 0}

private theorem sharpDiagram_vertices :
    sharpDiagram.diagramVertices = {Finsupp.single 1 2, Finsupp.single 0 3} := by
  ext α
  simp only [mem_diagramVertices_iff, Minimal, sharpDiagram, mem_ofPred, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hα, hmin⟩
    rcases hα with h1 | h0
    · left
      have hle : Finsupp.single (1 : Fin 2) 2 ≤ α := Finsupp.single_le_iff.mpr h1
      exact le_antisymm (hmin (Or.inl (by simp)) hle) hle
    · right
      have hle : Finsupp.single (0 : Fin 2) 3 ≤ α := Finsupp.single_le_iff.mpr h0
      exact le_antisymm (hmin (Or.inr (by simp)) hle) hle
  · rintro (rfl | rfl)
    · refine ⟨Or.inl (by simp), fun γ hγ hle ↦ ?_⟩
      have hγ0 : γ 0 = 0 := Nat.eq_zero_of_le_zero (by simpa using hle 0)
      exact Finsupp.single_le_iff.mpr (hγ.resolve_right (by omega))
    · refine ⟨Or.inr (by simp), fun γ hγ hle ↦ ?_⟩
      have hγ1 : γ 1 = 0 := Nat.eq_zero_of_le_zero (by simpa using hle 1)
      exact Finsupp.single_le_iff.mpr (hγ.resolve_left (by omega))

open scoped Classical in
private noncomputable def sharpGenerators :
    sharpDiagram.diagramVertices → MvPolynomial (Fin 2) ℤ :=
  fun v ↦ if v.1 = Finsupp.single 1 2 then X 0 ^ 2 + X 0 * X 1 else X 1 ^ 3

private theorem isHomogeneous_sharpGenerators (v : sharpDiagram.diagramVertices) :
    (sharpGenerators v).IsHomogeneous v.1.degree := by
  obtain ⟨v, hv⟩ := v
  rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · simp only [sharpGenerators, ite_true, Finsupp.degree_single]
    exact ((isHomogeneous_X ℤ (0 : Fin 2)).pow 2).add
      ((isHomogeneous_X ℤ (0 : Fin 2)).mul (isHomogeneous_X ℤ 1))
  · have hne : (Finsupp.single 0 3 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := fun h ↦ by
      simpa using congrArg (· (0 : Fin 2)) h
    simp only [sharpGenerators, hne, ite_false, Finsupp.degree_single]
    exact (isHomogeneous_X ℤ (1 : Fin 2)).pow 3

private theorem mem_diagramBox_sharpDiagram_single_one_two (β : Fin 2 →₀ ℕ) :
    β ∈ sharpDiagram.diagramBox (Finsupp.single 1 2) :=
  mem_diagramBox_iff.mpr fun α' hα' hlt ↦ by
    rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hα'
    rcases hα' with rfl | rfl
    · exact absurd hlt (lt_irrefl _)
    · exact absurd hlt (not_lt_of_gt (Finsupp.DegLex.lt_iff.mpr (Or.inl (by simp))))

private theorem monomial_mem_span_sharpDiagram_three {s : Fin 2 →₀ ℕ} (hs : s.degree = 3) :
    monomial s (1 : ℤ) ∈ Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 3) := by
  have hv₁ : Finsupp.single (1 : Fin 2) 2 ∈ sharpDiagram.diagramVertices := by
    rw [sharpDiagram_vertices]; simp
  have hv₂ : Finsupp.single (0 : Fin 2) 3 ∈ sharpDiagram.diagramVertices := by
    rw [sharpDiagram_vertices]; simp
  have hne : (Finsupp.single 0 3 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := fun h ↦ by
    simpa using congrArg (· (0 : Fin 2)) h
  have hm21 : monomial (Finsupp.single 0 2 + Finsupp.single 1 1) (1 : ℤ) ∈
      Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 3) :=
    Submodule.subset_span (monomial_mem_diagramSpanSet (by simp [sharpDiagram]) (by simp))
  have hg1 := Submodule.subset_span (R := ℤ)
    (monomial_mul_mem_diagramSpanSet (H := sharpGenerators) (ℓ := 3) ⟨_, hv₁⟩
      (mem_diagramBox_sharpDiagram_single_one_two (Finsupp.single 0 1)) (by simp))
  have hg2 := Submodule.subset_span (R := ℤ)
    (monomial_mul_mem_diagramSpanSet (H := sharpGenerators) (ℓ := 3) ⟨_, hv₁⟩
      (mem_diagramBox_sharpDiagram_single_one_two (Finsupp.single 1 1)) (by simp))
  have hs_deg : s 0 + s 1 = 3 := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hs
  rcases (by omega : s 0 = 0 ∨ s 0 = 1 ∨ s 0 = 2 ∨ s 0 = 3) with h0 | h0 | h0 | h0
  · have hs_eq : s = Finsupp.single 1 3 := by ext i; fin_cases i <;> simp <;> omega
    have hgen : monomial (0 : Fin 2 →₀ ℕ) 1 * sharpGenerators ⟨_, hv₂⟩ =
        monomial (Finsupp.single (1 : Fin 2) 3) 1 := by
      simp [sharpGenerators, hne, X_pow_eq_monomial]
    exact hs_eq ▸ hgen ▸ Submodule.subset_span (R := ℤ)
      (monomial_mul_mem_diagramSpanSet (H := sharpGenerators) (ℓ := 3)
        ⟨_, hv₂⟩ (zero_mem_diagramBox hv₂) (by simp))
  · have hs_eq : s = Finsupp.single 0 1 + Finsupp.single 1 2 := by
      ext i; fin_cases i <;> simp <;> omega
    have heq : monomial (Finsupp.single (1 : Fin 2) 1) 1 * sharpGenerators ⟨_, hv₁⟩ -
        monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 =
        monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 1 := by
      simp [sharpGenerators, mul_add, pow_two, X, monomial_mul_monomial, ← Finsupp.single_add,
        add_comm, add_left_comm]
    exact hs_eq ▸ heq ▸ sub_mem hg2 hm21
  · have hs_eq : s = Finsupp.single 0 2 + Finsupp.single 1 1 := by
      ext i; fin_cases i <;> simp <;> omega
    exact hs_eq ▸ hm21
  · have hs_eq : s = Finsupp.single 0 3 := by ext i; fin_cases i <;> simp <;> omega
    have heq : monomial (Finsupp.single (0 : Fin 2) 1) 1 * sharpGenerators ⟨_, hv₁⟩ -
        monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 = monomial (Finsupp.single 0 3) 1 := by
      simp [sharpGenerators, mul_add, pow_two, X, monomial_mul_monomial, ← add_assoc,
        ← Finsupp.single_add]
    exact hs_eq ▸ heq ▸ sub_mem hg1 hm21

private theorem sharpDiagram_span_three :
    Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 3) =
      homogeneousSubmodule (Fin 2) ℤ 3 := by
  apply le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule isHomogeneous_sharpGenerators 3)
  intro p hp
  have hp_val : ∑ s, ((TauCeti.homogeneousMonomialBasis (σ := Fin 2) (R := ℤ) 3).repr ⟨p, hp⟩ s •
      (TauCeti.homogeneousMonomialBasis (σ := Fin 2) (R := ℤ) 3 s : MvPolynomial (Fin 2) ℤ)) =
      p := by
    simpa only [Submodule.coe_sum, SetLike.val_smul] using
      congrArg Subtype.val
        ((TauCeti.homogeneousMonomialBasis (σ := Fin 2) (R := ℤ) 3).sum_repr ⟨p, hp⟩)
  rw [← hp_val]
  refine Submodule.sum_mem _ fun s _ ↦ ?_
  rw [TauCeti.coe_homogeneousMonomialBasis]
  exact Submodule.smul_mem _ _ (monomial_mem_span_sharpDiagram_three s.2)

private theorem sharpDiagram_span_five_ne :
    Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 5) ≠
      homogeneousSubmodule (Fin 2) ℤ 5 := by
  have hv₁ : Finsupp.single (1 : Fin 2) 2 ∈ sharpDiagram.diagramVertices := by
    rw [sharpDiagram_vertices]; simp
  intro hspan5
  have hmem5 : (X 1 ^ 5 : MvPolynomial (Fin 2) ℤ) ∈
      Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 5) := by
    rw [hspan5, mem_homogeneousSubmodule]
    exact (isHomogeneous_X ℤ (1 : Fin 2)).pow 5
  have hker : Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 5) ≤
      LinearMap.ker (aeval (R := ℤ) ![0, (1 : ℤ)]).toLinearMap := by
    refine Submodule.span_le.mpr fun g hg ↦ ?_
    simp only [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    rcases hg with ⟨⟨v, hv⟩, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
    · rw [map_mul]
      have hv_cases := hv
      rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hv_cases
      rcases hv_cases with rfl | rfl
      · simp [sharpGenerators]
      · have hβ_deg : β 0 + β 1 = 2 := by
          rw [Finsupp.degree_single, Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
          omega
        have hlt_v : toDegLex (Finsupp.single (1 : Fin 2) 2) < toDegLex (Finsupp.single 0 3) :=
          Finsupp.DegLex.lt_iff.mpr (Or.inl (by simp))
        have hβ1_lt : β 1 < 2 := by
          by_contra! hge
          exact (mem_diagramBox_iff.mp hβ) _ hv₁ hlt_v
            (Finsupp.single_le_iff.mpr (by simpa using hge))
        have hle0 : Finsupp.single (0 : Fin 2) 1 ≤ β := Finsupp.single_le_iff.mpr (by omega)
        have hmul : monomial β (1 : ℤ) = X 0 * monomial (β - Finsupp.single 0 1) 1 := by
          rw [X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle0]
        rw [hmul, map_mul]
        simp
    · exfalso
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      exact hγ (by simp [sharpDiagram]; omega)
  have hzero := hker hmem5
  simp only [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hzero
  simp at hzero

/-- Sharpness of `Set.diagramCutoff`: in two variables (`Fin 2`), there exist an upward-closed
monotone diagram `D` whose vertices have degree at most `3` (`D.diagramCutoff = 6`) and homogeneous
polynomials `H` over `ℤ` such that `D.diagramSpanSet H 3` spans `homogeneousSubmodule (Fin 2) ℤ 3`
at `3 = max_{v ∈ D.diagramVertices} v.degree`, yet `D.diagramSpanSet H 5` fails to span
`homogeneousSubmodule (Fin 2) ℤ 5`. Thus `D.diagramCutoff` in `Set.span_diagramSpanSet_eq_of_le`
cannot be lowered to the maximum vertex degree. -/
theorem exists_monotone_diagram_span_lt_diagramCutoff_not_span :
    ∃ (D : Set (Fin 2 →₀ ℕ)) (H : D.diagramVertices → MvPolynomial (Fin 2) ℤ),
      IsUpperSet D ∧ D.IsMonotoneDiagram ∧ (∀ v, (H v).IsHomogeneous v.1.degree) ∧
      (∀ v : D.diagramVertices, v.1.degree ≤ 3) ∧
      Submodule.span ℤ (D.diagramSpanSet H 3) = homogeneousSubmodule (Fin 2) ℤ 3 ∧
      Submodule.span ℤ (D.diagramSpanSet H 5) ≠ homogeneousSubmodule (Fin 2) ℤ 5 := by
  refine ⟨sharpDiagram, sharpGenerators,
    fun α β hle hα ↦ hα.imp (fun h ↦ h.trans (hle 1)) (fun h ↦ h.trans (hle 0)), ?_,
    isHomogeneous_sharpGenerators, ?_, sharpDiagram_span_three, sharpDiagram_span_five_ne⟩
  · refine isMonotoneDiagram_iff.mpr fun α hα i j hij ↦ ?_
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] at hij ⊢
    · exact absurd hij (lt_irrefl _)
    · refine Or.inl ?_
      rw [Finsupp.transferExp_apply_right α (i := 0) (j := 1) (by decide)]
      rcases hα with h1 | h0 <;> omega
    · exact absurd hij (by decide)
    · exact absurd hij (lt_irrefl _)
  · rintro ⟨v, hv⟩
    rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp

end CutoffSharpness

end ChecksAndSharpness

end Set
