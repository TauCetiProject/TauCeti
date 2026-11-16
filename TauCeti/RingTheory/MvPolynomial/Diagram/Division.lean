/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Data.Finsupp.Diagram
import TauCeti.Data.Finsupp.Fin
import TauCeti.Data.Finsupp.Order
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Bierstone–Milman's finite-degree criterion for monotone diagrams

Given a diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ`, a commutative
semiring `A`, and homogeneous polynomials `H : D.diagramVertices → MvPolynomial σ A` of degrees
`v.1.degree`, Bierstone and Milman (1997, §8, pp. 274–275) define in each degree `ℓ : ℕ` the
family `D.diagramSpanSet H ℓ` of supported multiples `monomial β 1 * H v` (`β ∈ D.diagramBox v.1`,
`v.1.degree + β.degree = ℓ`) and complementary monomials `monomial γ 1` (`γ ∉ D`, `γ.degree = ℓ`).

**Theorem 8.1 (`Set.span_diagramSpanSet_eq_of_le`)** proves that over a commutative ring `A`, if
`D` is upward closed and monotone (`D.IsMonotoneDiagram`) and `D.diagramSpanSet H k` spans
`homogeneousSubmodule σ A k` at some degree `k ≥ D.diagramCutoff`, then `D.diagramSpanSet H ℓ`
spans `homogeneousSubmodule σ A ℓ` for every `ℓ ≥ k`. We also prove boundary cases (`D = ∅`,
`D = Set.univ`, degrees strictly below all elements of `D`, and principal cones `Set.Ici α` in
one variable) and true sharpness of `Set.diagramCutoff`
(`TauCeti.exists_isMonotoneDiagram_forall_lt_diagramCutoff_and_span_ne`, exhibiting an upward-closed
monotone diagram `D` on `Fin 2` with `0 < D.diagramCutoff` whose division family spans in every
degree `k < D.diagramCutoff` yet fails to span in degree `D.diagramCutoff`). For the block division
endomorphism and cutoff determinant, see `TauCeti.RingTheory.MvPolynomial.Diagram.CutoffDet`.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Theorem 8.1 and Definition 8.3, pp. 274–275.
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

/-- Relabeling variables along an order isomorphism `e : τ ≃o σ` transports `diagramSpanSet`. -/
theorem image_renameEquiv_diagramSpanSet {τ : Type*} [Finite τ] [LinearOrder τ] (e : τ ≃o σ)
    (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (renameEquiv A e.toEquiv) ''
        ((Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramSpanSet
          (fun v₀ ↦ (renameEquiv A e.toEquiv).symm
            (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
              (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩)) ℓ) =
      D.diagramSpanSet H ℓ := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨q, (⟨v₀, β₀, hβ₀, hdeg₀, rfl⟩ | ⟨γ₀, hγ₀, hdeg₀, rfl⟩), rfl⟩
    · rw [map_mul, AlgEquiv.apply_symm_apply, renameEquiv_apply, rename_monomial,
        ← Finsupp.equivMapDomain_eq_mapDomain]
      exact monomial_mul_mem_diagramSpanSet
        ⟨Finsupp.equivMapDomain e.toEquiv v₀.1,
          (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.2⟩
        ((mem_diagramBox_preimage_equivMapDomain_iff e).mp hβ₀)
        (by simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg₀)
    · rw [renameEquiv_apply, rename_monomial, ← Finsupp.equivMapDomain_eq_mapDomain]
      exact monomial_mem_diagramSpanSet hγ₀
        (by simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg₀)
  · rintro _ (⟨⟨v, hv⟩, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
    · obtain ⟨v₀, rfl⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective v
      obtain ⟨β₀, rfl⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective β
      simp only [Finsupp.domCongr_apply] at hv hβ hdeg ⊢
      have hv₀ : v₀ ∈ (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramVertices :=
        (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mpr hv
      have hβ₀ : β₀ ∈ (Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramBox v₀ :=
        (mem_diagramBox_preimage_equivMapDomain_iff e).mpr hβ
      have hdeg₀ : v₀.degree + β₀.degree = ℓ := by
        simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg
      refine ⟨monomial β₀ 1 * _, monomial_mul_mem_diagramSpanSet ⟨v₀, hv₀⟩ hβ₀ hdeg₀, ?_⟩
      rw [map_mul, AlgEquiv.apply_symm_apply, renameEquiv_apply, rename_monomial,
        ← Finsupp.equivMapDomain_eq_mapDomain]
    · obtain ⟨γ₀, rfl⟩ := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective γ
      simp only [Finsupp.domCongr_apply] at hγ hdeg ⊢
      have hdeg₀ : γ₀.degree = ℓ := by simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg
      refine ⟨monomial γ₀ 1, monomial_mem_diagramSpanSet hγ hdeg₀, ?_⟩
      simp [renameEquiv_apply, rename_monomial, Finsupp.equivMapDomain_eq_mapDomain]

/-- If every element of `D` has degree strictly greater than `ℓ`, then `D.diagramSpanSet H ℓ`
consists precisely of all monomials of degree `ℓ` (independently of `H`). -/
theorem diagramSpanSet_of_forall_lt_degree {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (hD : ∀ γ ∈ D, ℓ < γ.degree) (H : D.diagramVertices → MvPolynomial σ A) :
    D.diagramSpanSet H ℓ = {p | ∃ γ : σ →₀ ℕ, γ.degree = ℓ ∧ p = monomial γ 1} := by
  ext p
  simp only [mem_diagramSpanSet_iff, mem_ofPred]
  refine ⟨?_, fun ⟨γ, hdeg, hp⟩ ↦ Or.inr ⟨γ, fun hmem ↦ (hD γ hmem).ne' hdeg, hdeg, hp⟩⟩
  rintro (⟨v, β, _, hdeg, rfl⟩ | ⟨γ, _, hdeg, rfl⟩)
  · exact absurd (hD v.1 (D.diagramVertices_subset v.2)) (by omega)
  · exact ⟨γ, hdeg, rfl⟩

/-- If every element of `D` has degree strictly greater than `ℓ`, then `D.diagramSpanSet H ℓ`
spans `homogeneousSubmodule σ A ℓ` independently of `H`. -/
theorem span_diagramSpanSet_of_forall_lt_degree {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (hD : ∀ γ ∈ D, ℓ < γ.degree) (H : D.diagramVertices → MvPolynomial σ A) :
    Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [diagramSpanSet_of_forall_lt_degree hD]
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (homogeneousSubmodule_le_iff.mpr fun γ hdeg ↦ Submodule.subset_span ⟨γ, hdeg, rfl⟩)
  rintro _ ⟨γ, hdeg, rfl⟩
  exact (mem_homogeneousSubmodule ℓ _).mpr (isHomogeneous_monomial 1 hdeg)

theorem diagramSpanSet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ =
      {p | ∃ γ : σ →₀ ℕ, γ.degree = ℓ ∧ p = monomial γ 1} :=
  diagramSpanSet_of_forall_lt_degree (fun _ h ↦ False.elim h) H

/-- For `D = ∅`, the complementary monomials span every homogeneous degree independently of `H`. -/
@[simp]
theorem span_diagramSpanSet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (ℓ : ℕ) :
    Submodule.span A ((∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  span_diagramSpanSet_of_forall_lt_degree (fun _ h ↦ False.elim h) H

end SpanSet

section FiniteDegreeCriterion

variable {A : Type*} [CommRing A]

private theorem X_zero_mul_mem_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hm : D.diagramCutoff ≤ m)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ D.diagramSpanSet H m) :
    X 0 * g ∈ D.diagramSpanSet H (m + 1) := by
  rcases hg with ⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
  · rw [← mul_assoc, X, monomial_mul_monomial, mul_one]
    refine monomial_mul_mem_diagramSpanSet v
      (single_zero_add_mem_diagramBox hD_mono hβ (hdeg ▸ hm)) ?_
    rw [map_add, Finsupp.degree_single]; omega
  · rw [X, monomial_mul_monomial, mul_one]
    refine monomial_mem_diagramSpanSet
      (single_zero_add_notMem_of_notMem hD_up hD_mono hγ (hdeg ▸ hm)) ?_
    rw [map_add, Finsupp.degree_single, hdeg, add_comm]

private theorem X_zero_mul_mem_span_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hm : D.diagramCutoff ≤ m)
    (hspan_m : homogeneousSubmodule (Fin (n + 1)) A m ≤ Submodule.span A (D.diagramSpanSet H m))
    {Q : MvPolynomial (Fin (n + 1)) A} (hQ : Q.IsHomogeneous m) :
    X 0 * Q ∈ Submodule.span A (D.diagramSpanSet H (m + 1)) := by
  have hmap := Submodule.mem_map_of_mem (f := LinearMap.mulLeft A (X 0))
    (hspan_m ((mem_homogeneousSubmodule m Q).mpr hQ))
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span (X_zero_mul_mem_diagramSpanSet hD_up hD_mono hm hg)

private theorem killCompl_succ_mem_span_diagramSliceZero {n k : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hk : D.diagramCutoff ≤ k)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ D.diagramSpanSet H k) :
    g.killCompl (Fin.succ_injective n) ∈
      Submodule.span A
        (D.diagramSliceZero.diagramSpanSet
          (fun v' ↦
            (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩).killCompl
              (Fin.succ_injective n)) k) := by
  have h0_not : (0 : Fin (n + 1)) ∉ Set.range Fin.succ := by simp
  rcases hg with ⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
  · rw [map_mul]
    by_cases hβ0 : β 0 = 0
    · have hβ_eq : Finsupp.cons 0 β.tail = β := by rw [← hβ0, Finsupp.cons_tail]
      have hβ_map : β.tail.mapDomain Fin.succ = β := by rw [Finsupp.mapDomain_finSucc, hβ_eq]
      rw [← hβ_map, killCompl_monomial_mapDomain]
      by_cases hv0 : v.1 0 = 0
      · have hv_eq : Finsupp.cons 0 v.1.tail = v.1 := by rw [← hv0, Finsupp.cons_tail]
        have hv' : v.1.tail ∈ D.diagramSliceZero.diagramVertices :=
          mem_diagramVertices_diagramSliceZero_iff.mpr (hv_eq.symm ▸ v.2)
        have hβ' : β.tail ∈ D.diagramSliceZero.diagramBox v.1.tail :=
          cons_zero_mem_diagramBox_iff.mp (hv_eq.symm ▸ hβ_eq.symm ▸ hβ)
        have hdeg' : v.1.tail.degree + β.tail.degree = k := by
          have hv_d : v.1.degree = v.1.tail.degree := by
            simpa using (congrArg Finsupp.degree hv_eq).symm
          have hβ_d : β.degree = β.tail.degree := by
            simpa using (congrArg Finsupp.degree hβ_eq).symm
          omega
        have hv_sub : (⟨Finsupp.cons 0 v.1.tail,
            mem_diagramVertices_diagramSliceZero_iff.mp hv'⟩ : D.diagramVertices) = v :=
          Subtype.ext hv_eq
        exact hv_sub ▸ Submodule.subset_span
          (monomial_mul_mem_diagramSpanSet ⟨v.1.tail, hv'⟩ hβ' hdeg')
      · exact absurd (degree_add_lt_diagramCutoff_of_mem_diagramBox hD_mono v.2
          (Nat.pos_of_ne_zero hv0) hβ hβ0) (by omega)
    · rw [killCompl_monomial_eq_zero_of_notMem_range _ _ (Finsupp.mem_support_iff.mpr hβ0) h0_not,
        zero_mul]
      exact zero_mem _
  · by_cases hγ0 : γ 0 = 0
    · have hγ_eq : Finsupp.cons 0 γ.tail = γ := by rw [← hγ0, Finsupp.cons_tail]
      have hγ_map : γ.tail.mapDomain Fin.succ = γ := by rw [Finsupp.mapDomain_finSucc, hγ_eq]
      rw [← hγ_map, killCompl_monomial_mapDomain]
      exact Submodule.subset_span (monomial_mem_diagramSpanSet
        (fun hm ↦ hγ (hγ_eq ▸ D.mem_diagramSliceZero_iff.mp hm))
        (by simpa [hdeg] using congrArg Finsupp.degree hγ_eq))
    · rw [killCompl_monomial_eq_zero_of_notMem_range _ _ (Finsupp.mem_support_iff.mpr hγ0) h0_not]
      exact zero_mem _

private theorem span_diagramSliceZero_of_span {n k : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hk : D.diagramCutoff ≤ k)
    (hspan : homogeneousSubmodule (Fin (n + 1)) A k ≤ Submodule.span A (D.diagramSpanSet H k)) :
    homogeneousSubmodule (Fin n) A k ≤
      Submodule.span A
        (D.diagramSliceZero.diagramSpanSet
          (fun v' ↦
            (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩).killCompl
              (Fin.succ_injective n)) k) := by
  intro q hq
  have hq_hom : (rename Fin.succ q).IsHomogeneous k :=
    (IsHomogeneous.rename_isHomogeneous_iff (Fin.succ_injective n)).mpr
      ((mem_homogeneousSubmodule k q).mp hq)
  have hmap := Submodule.mem_map_of_mem
    (f := (killCompl (R := A) (Fin.succ_injective n)).toLinearMap)
    (hspan ((mem_homogeneousSubmodule k _).mpr hq_hom))
  rw [AlgHom.toLinearMap_apply, killCompl_rename_app, Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨g, hg, rfl⟩
  exact killCompl_succ_mem_span_diagramSliceZero hD_mono hk hg

private theorem rename_succ_mem_span_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) (hm : D.diagramCutoff ≤ m)
    (ihm : homogeneousSubmodule (Fin (n + 1)) A m ≤ Submodule.span A (D.diagramSpanSet H m))
    {g' : MvPolynomial (Fin n) A}
    (hg' : g' ∈ D.diagramSliceZero.diagramSpanSet
      (fun v' ↦
        (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩).killCompl
          (Fin.succ_injective n)) (m + 1)) :
    rename Fin.succ g' ∈ Submodule.span A (D.diagramSpanSet H (m + 1)) := by
  rcases hg' with ⟨v', β', hβ', hdeg', rfl⟩ | ⟨γ', hγ', hdeg', rfl⟩
  · let v : D.diagramVertices :=
      ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩
    let Q : MvPolynomial (Fin (n + 1)) A := monomial (Finsupp.cons 0 β') 1 * H v
    have hQ_mem : Q ∈ D.diagramSpanSet H (m + 1) :=
      monomial_mul_mem_diagramSpanSet v (cons_zero_mem_diagramBox_iff.mpr hβ') (by simpa [v])
    obtain ⟨R, hR_hom, hQ_split⟩ :=
      (isHomogeneous_of_mem_diagramSpanSet hH hQ_mem).exists_eq_rename_succ_add_X_zero_mul
    have hkQ : Q.killCompl (Fin.succ_injective n) =
        monomial β' 1 * (H v).killCompl (Fin.succ_injective n) := by
      rw [map_mul, ← Finsupp.mapDomain_finSucc, killCompl_monomial_mapDomain]
    rw [hkQ] at hQ_split
    rw [eq_sub_of_add_eq hQ_split.symm]
    exact sub_mem (Submodule.subset_span hQ_mem)
      (X_zero_mul_mem_span_diagramSpanSet hD_up hD_mono hm ihm hR_hom)
  · rw [rename_monomial, Finsupp.mapDomain_finSucc]
    exact Submodule.subset_span
      (monomial_mem_diagramSpanSet (mt D.mem_diagramSliceZero_iff.mpr hγ') (by simpa using hdeg'))

private theorem homogeneousSubmodule_le_span_fin :
    ∀ {d : ℕ} {D : Set (Fin d →₀ ℕ)} (_hD_up : IsUpperSet D) (_hD_mono : D.IsMonotoneDiagram)
      {H : D.diagramVertices → MvPolynomial (Fin d) A}
      (_hH : ∀ v, (H v).IsHomogeneous v.1.degree) {k : ℕ} (_hk : D.diagramCutoff ≤ k)
      (_hspan : homogeneousSubmodule (Fin d) A k ≤ Submodule.span A (D.diagramSpanSet H k))
      {ℓ : ℕ} (_hℓ : k ≤ ℓ),
      homogeneousSubmodule (Fin d) A ℓ ≤ Submodule.span A (D.diagramSpanSet H ℓ)
  | 0, _, _, _, _, _, _, _, hspan, ℓ, hℓ => by
    rcases hℓ.eq_or_lt with rfl | hlt
    · exact hspan
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hlt)
      rw [MvPolynomial.homogeneousSubmodule_succ_eq_bot_of_isEmpty]; exact bot_le
  | n + 1, D, hD_up, hD_mono, H, hH, k, hk, hspan, ℓ, hℓ => by
    let H' : D.diagramSliceZero.diagramVertices → MvPolynomial (Fin n) A :=
      fun v' ↦ (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩).killCompl
        (Fin.succ_injective n)
    have hH' : ∀ v', (H' v').IsHomogeneous v'.1.degree := fun v' ↦ by
      simpa [H'] using
        (hH ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩).killCompl
          (Fin.succ_injective n)
    have hspan' (m : ℕ) (hm : k ≤ m) :
        homogeneousSubmodule (Fin n) A m ≤
          Submodule.span A (D.diagramSliceZero.diagramSpanSet H' m) :=
      homogeneousSubmodule_le_span_fin hD_up.diagramSliceZero hD_mono.diagramSliceZero hH'
        ((diagramCutoff_diagramSliceZero_le D).trans hk)
        (span_diagramSliceZero_of_span hD_mono hk hspan) hm
    induction ℓ, hℓ using Nat.le_induction with
    | base => exact hspan
    | succ m hm ihm =>
      intro P hP
      obtain ⟨Q, hQ_hom, hP_split⟩ :=
        ((mem_homogeneousSubmodule (m + 1) P).mp hP).exists_eq_rename_succ_add_X_zero_mul
      rw [hP_split]
      refine add_mem ?_ (X_zero_mul_mem_span_diagramSpanSet hD_up hD_mono (hk.trans hm) ihm hQ_hom)
      have hkP := hspan' (m + 1) (hm.trans (Nat.le_succ m))
        ((mem_homogeneousSubmodule (m + 1) _).mpr
          (((mem_homogeneousSubmodule (m + 1) P).mp hP).killCompl (Fin.succ_injective n)))
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
    have hp₀_hom : ((renameEquiv A e.toEquiv).symm p).IsHomogeneous m := by
      rw [renameEquiv_symm, renameEquiv_apply,
        IsHomogeneous.rename_isHomogeneous_iff e.toEquiv.symm.injective]
      exact (mem_homogeneousSubmodule m p).mp hp
    have hmem := Submodule.mem_map_of_mem (f := (renameEquiv A e.toEquiv).toLinearMap)
      (hle ((mem_homogeneousSubmodule m _).mpr hp₀_hom))
    rw [AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply] at hmem
    rwa [hmap_span]
  · intro hle q hq
    have hq_hom : ((renameEquiv A e.toEquiv) q).IsHomogeneous m := by
      rw [renameEquiv_apply, IsHomogeneous.rename_isHomogeneous_iff e.toEquiv.injective]
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
  have hD₀_up : IsUpperSet D₀ := fun _ _ hle hα ↦
    hD_up (by simpa using hle) hα
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
    (homogeneousSubmodule_le_span_fin hD₀_up
      ((isMonotoneDiagram_preimage_equivMapDomain e).mpr hD_mono) hH₀ hk₀
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
    refine ⟨?_, fun h ↦ h ▸ ⟨v₀, 0, by simp [v₀], by simp [v₀], by simp⟩⟩
    rintro ⟨⟨v, hv⟩, β, _, hdeg, rfl⟩
    obtain rfl : v = 0 := by simpa using hv
    obtain rfl : β = 0 := by rw [← Finsupp.degree_eq_zero_iff]; simpa using hdeg
    simp [v₀]
  rw [hset, hv₀_eq, isUnit_iff_exists_inv']
  refine ⟨fun hspan ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · have h1 : (1 : MvPolynomial σ A) ∈ Submodule.span A {C (constantCoeff (H v₀))} := by
      rw [hspan, mem_homogeneousSubmodule]; exact isHomogeneous_one σ A
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
    exact ⟨a, by simpa [smul_eq_C_mul] using congrArg constantCoeff ha⟩
  · refine le_antisymm (hv₀_eq ▸ hset ▸ span_diagramSpanSet_le_homogeneousSubmodule hH 0)
      fun p hp ↦ ?_
    have hp0 : p.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 p).mp hp
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp0
    rw [constantCoeff_C] at ha
    rw [hp0, Submodule.mem_span_singleton]
    exact ⟨p.coeff 0 * a, by rw [smul_eq_C_mul, ← map_mul, mul_assoc, ha, mul_one]⟩

/-- For `D = Set.univ`, `D.diagramSpanSet H ℓ` spans in *all* degrees `ℓ : ℕ` if and only if
`constantCoeff (H ⟨0, _⟩)` is a unit in `A`. -/
theorem forall_span_diagramSpanSet_univ_iff
    {H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    (∀ ℓ : ℕ, Submodule.span A ((Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ) =
        homogeneousSubmodule σ A ℓ) ↔
      IsUnit (constantCoeff (H ⟨0, by simp⟩)) := by
  refine ⟨fun h ↦ (span_diagramSpanSet_univ_zero_iff hH).mp (h 0), fun hu ℓ ↦ ?_⟩
  let v₀ : (Set.univ : Set (σ →₀ ℕ)).diagramVertices := ⟨0, by simp⟩
  have hv₀_eq : H v₀ = C (constantCoeff (H v₀)) := by
    have h0 : (H v₀).IsHomogeneous 0 := by simpa [v₀] using hH v₀
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h0
    conv_lhs => rw [h0]
    conv_rhs => rw [h0, constantCoeff_C]
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv'.mp hu
  refine le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule hH ℓ)
    (homogeneousSubmodule_le_iff.mpr fun γ hdeg ↦ ?_)
  have hmem : monomial γ 1 * H v₀ ∈ (Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ :=
    monomial_mul_mem_diagramSpanSet v₀ (by simp [v₀]) (by simp [v₀, hdeg])
  have heq : a • (monomial γ 1 * H v₀) = monomial γ (1 : A) := by
    rw [hv₀_eq, smul_eq_C_mul, mul_left_comm, ← map_mul, ha, C_1, mul_one]
  exact heq ▸ Submodule.smul_mem _ a (Submodule.subset_span hmem)

/-- For any principal cone `Set.Ici α` and degree `ℓ < α.degree`, `diagramSpanSet` spans
`homogeneousSubmodule σ A ℓ` unconditionally (independently of `H`). -/
theorem span_diagramSpanSet_Ici_of_lt {α : σ →₀ ℕ} {ℓ : ℕ} (hℓ : ℓ < α.degree)
    (H : (Set.Ici α).diagramVertices → MvPolynomial σ A) :
    Submodule.span A ((Set.Ici α).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  span_diagramSpanSet_of_forall_lt_degree
    (fun _ hγ ↦ lt_of_lt_of_le hℓ (Finsupp.degree_mono hγ)) H

/-- In a single variable (`[Unique σ]`), for the cone `D = Set.Ici α` and `α.degree ≤ ℓ`,
`D.diagramSpanSet H ℓ` spans `homogeneousSubmodule σ A ℓ` if and only if `(H ⟨α, _⟩).coeff α` is
a unit in `A`. -/
theorem span_diagramSpanSet_Ici_iff [Unique σ] {α : σ →₀ ℕ} {ℓ : ℕ} (haℓ : α.degree ≤ ℓ)
    {H : (Set.Ici α).diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    Submodule.span A ((Set.Ici α).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ ↔
      IsUnit ((H ⟨α, by simp⟩).coeff α) := by
  have hsingle (γ : σ →₀ ℕ) : γ = Finsupp.single (default : σ) γ.degree := by
    have h := congrArg Finsupp.degree (Finsupp.unique_single γ)
    rw [Finsupp.degree_single] at h
    rw [h]
    exact Finsupp.unique_single γ
  let v₀ : (Set.Ici α).diagramVertices := ⟨α, by simp⟩
  have hv₀_eq : H v₀ = monomial α ((H v₀).coeff α) := by
    simpa only [v₀, ← hsingle α] using (hH v₀).eq_monomial_single_default
  have hmul : monomial (Finsupp.single (default : σ) (ℓ - α.degree)) 1 * H v₀ =
      monomial (Finsupp.single default ℓ) ((H v₀).coeff α) := by
    conv_lhs => rw [hv₀_eq]
    rw [monomial_mul_monomial, one_mul]
    have hadd : Finsupp.single (default : σ) (ℓ - α.degree) + α = Finsupp.single default ℓ := by
      conv_lhs => rw [hsingle α]
      rw [← Finsupp.single_add, Finsupp.degree_single, Nat.sub_add_cancel haℓ]
    rw [hadd]
  have hset : (Set.Ici α).diagramSpanSet H ℓ =
      {monomial (Finsupp.single (default : σ) ℓ) ((H v₀).coeff α)} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr (hmul ▸ monomial_mul_mem_diagramSpanSet v₀
      (by simp [v₀]) (by dsimp only [v₀]; rw [Finsupp.degree_single]; omega)))
    rintro _ (⟨⟨v, hv⟩, β, _, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
    · have hveq : v = α := by simpa using hv
      have hdeg' : α.degree + β.degree = ℓ := hveq ▸ hdeg
      obtain rfl : β = Finsupp.single default (ℓ - α.degree) := by
        rw [hsingle β]; congr 1; omega
      have hv_sub : (⟨v, hv⟩ : (Set.Ici α).diagramVertices) = v₀ := Subtype.ext hveq
      rw [hv_sub]
      exact mem_singleton_iff.mpr hmul
    · exact False.elim (hγ (by
        rw [hsingle α, hsingle γ, hdeg, mem_Ici, Finsupp.single_le_iff, Finsupp.single_eq_same]
        exact haℓ))
  rw [hset, isUnit_iff_exists_inv']
  refine ⟨fun hspan ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · have hm : monomial (Finsupp.single (default : σ) ℓ) (1 : A) ∈
        Submodule.span A {monomial (Finsupp.single default ℓ) ((H v₀).coeff α)} := by
      rw [hspan, mem_homogeneousSubmodule]
      exact isHomogeneous_monomial 1 (Finsupp.degree_single default ℓ)
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨u, ?_⟩
    simpa [smul_monomial] using
      congrArg (fun q : MvPolynomial σ A ↦ q.coeff (Finsupp.single default ℓ)) hu
  · refine le_antisymm (hset ▸ span_diagramSpanSet_le_homogeneousSubmodule hH ℓ) fun p hp ↦ ?_
    rw [((mem_homogeneousSubmodule ℓ p).mp hp).eq_monomial_single_default,
      Submodule.mem_span_singleton]
    exact ⟨p.coeff (Finsupp.single default ℓ) * u, by
      rw [smul_monomial, smul_eq_mul, mul_assoc, hu, mul_one]⟩

end BoundaryCases

end Set

namespace TauCeti

section CutoffSharpness

private def sharpDiagram : Set (Fin 2 →₀ ℕ) :=
  {γ | 3 ≤ γ 1 ∨ 3 ≤ γ 0}

private theorem sharpDiagram_vertices :
    sharpDiagram.diagramVertices = {Finsupp.single 1 3, Finsupp.single 0 3} := by
  ext α
  simp only [Set.mem_diagramVertices_iff, Minimal, sharpDiagram, Set.mem_ofPred, Finset.mem_insert,
    Finset.mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨h1 | h0, hmin⟩
    · exact Or.inl <| le_antisymm (hmin (Or.inl (by simp)) (Finsupp.single_le_iff.mpr h1))
        (Finsupp.single_le_iff.mpr h1)
    · exact Or.inr <| le_antisymm (hmin (Or.inr (by simp)) (Finsupp.single_le_iff.mpr h0))
        (Finsupp.single_le_iff.mpr h0)
  · rintro (rfl | rfl)
    · refine ⟨Or.inl (by simp), fun γ hγ hle ↦ ?_⟩
      have hγ0 : γ 0 = 0 := Nat.eq_zero_of_le_zero (by simpa using hle 0)
      exact Finsupp.single_le_iff.mpr (hγ.resolve_right (by omega))
    · refine ⟨Or.inr (by simp), fun γ hγ hle ↦ ?_⟩
      have hγ1 : γ 1 = 0 := Nat.eq_zero_of_le_zero (by simpa using hle 1)
      exact Finsupp.single_le_iff.mpr (hγ.resolve_left (by omega))

private theorem sharpDiagram_diagramCutoff : sharpDiagram.diagramCutoff = 6 := by
  have hslice : sharpDiagram.diagramSliceZero = Set.Ici (Finsupp.single (0 : Fin 1) 3) := by
    ext γ'
    have h1 : (Finsupp.cons 0 γ') (1 : Fin 2) = γ' 0 := Finsupp.cons_succ 0 0 γ'
    simp [Set.mem_diagramSliceZero_iff, sharpDiagram, Set.mem_Ici, Finsupp.single_le_iff, h1]
  have hcut1 : (Set.Ici (Finsupp.single (0 : Fin 1) 3)).diagramCutoff = 4 := by
    rw [Set.diagramCutoff_fin_succ]
    simp [Set.diagramVertices_Ici, Finset.filter_singleton]
  rw [Set.diagramCutoff_fin_succ, hslice, hcut1, sharpDiagram_vertices]
  simp [Finset.filter_insert, Finset.filter_singleton]

private theorem toDegLex_sharpDiagram_lt :
    toDegLex (Finsupp.single (1 : Fin 2) 3) < toDegLex (Finsupp.single 0 3) := by
  rw [Finsupp.DegLex.lt_iff]
  refine Or.inr ⟨by simp, ?_⟩
  rw [Finsupp.Lex.lt_iff]
  exact ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), by simp⟩

open scoped Classical in
private noncomputable def sharpGenerators (A : Type*) [CommSemiring A] :
    sharpDiagram.diagramVertices → MvPolynomial (Fin 2) A :=
  fun v ↦ if v.1 = Finsupp.single 1 3 then X 0 ^ 3 else X 1 ^ 3

private theorem isHomogeneous_sharpGenerators (A : Type*) [CommSemiring A]
    (v : sharpDiagram.diagramVertices) :
    (sharpGenerators A v).IsHomogeneous v.1.degree := by
  obtain ⟨v, hv⟩ := v
  rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · simp only [sharpGenerators, ite_true, Finsupp.degree_single]
    exact (isHomogeneous_X A (0 : Fin 2)).pow 3
  · have hne : (Finsupp.single (0 : Fin 2) 3) ≠ Finsupp.single 1 3 := fun h ↦ by
      simpa using congrArg (· (0 : Fin 2)) h
    simp only [sharpGenerators, hne, ite_false, Finsupp.degree_single]
    exact (isHomogeneous_X A (1 : Fin 2)).pow 3

private theorem mem_diagramBox_sharpDiagram_single_one_three (β : Fin 2 →₀ ℕ) :
    β ∈ sharpDiagram.diagramBox (Finsupp.single 1 3) :=
  Set.mem_diagramBox_iff.mpr fun α' hα' hlt ↦ by
    rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hα'
    rcases hα' with rfl | rfl
    · exact absurd hlt (lt_irrefl _)
    · exact absurd hlt (not_lt_of_gt toDegLex_sharpDiagram_lt)

private theorem mem_diagramBox_sharpDiagram_single_zero_three_iff (β : Fin 2 →₀ ℕ) :
    β ∈ sharpDiagram.diagramBox (Finsupp.single 0 3) ↔ β 1 < 3 := by
  have hv₁ : Finsupp.single (1 : Fin 2) 3 ∈ sharpDiagram.diagramVertices := by
    rw [sharpDiagram_vertices]; simp
  refine ⟨fun hβ ↦ ?_, fun hlt1 ↦ Set.mem_diagramBox_iff.mpr fun α' hα' hlt hle ↦ ?_⟩
  · by_contra! hge
    exact (Set.mem_diagramBox_iff.mp hβ) _ hv₁ toDegLex_sharpDiagram_lt
      (Finsupp.single_le_iff.mpr (by simpa using hge))
  · rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hα'
    rcases hα' with rfl | rfl
    · have h1 := hle 1
      simp at h1
      omega
    · exact absurd hlt (lt_irrefl _)

private theorem sharpDiagram_span_of_lt_six (A : Type*) [CommSemiring A] {k : ℕ} (hk : k < 6) :
    Submodule.span A (sharpDiagram.diagramSpanSet (sharpGenerators A) k) =
      homogeneousSubmodule (Fin 2) A k := by
  have hv₁ : Finsupp.single (1 : Fin 2) 3 ∈ sharpDiagram.diagramVertices := by
    rw [sharpDiagram_vertices]; simp
  have hv₂ : Finsupp.single (0 : Fin 2) 3 ∈ sharpDiagram.diagramVertices := by
    rw [sharpDiagram_vertices]; simp
  have hne : (Finsupp.single (0 : Fin 2) 3) ≠ Finsupp.single 1 3 := fun h ↦ by
    simpa using congrArg (· (0 : Fin 2)) h
  refine le_antisymm
    (Set.span_diagramSpanSet_le_homogeneousSubmodule (isHomogeneous_sharpGenerators A) k)
    (homogeneousSubmodule_le_iff.mpr fun s hs ↦ Submodule.subset_span ?_)
  have hs_sum : s 0 + s 1 = k := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hs
  by_cases hs0 : 3 ≤ s 0
  · let β : Fin 2 →₀ ℕ := s - Finsupp.single 0 3
    have hle : Finsupp.single (0 : Fin 2) 3 ≤ s := Finsupp.single_le_iff.mpr hs0
    have hmul : monomial β 1 * sharpGenerators A ⟨_, hv₁⟩ = monomial s (1 : A) := by
      simp [sharpGenerators, X_pow_eq_monomial, monomial_mul_monomial, β,
        tsub_add_cancel_of_le hle]
    have hdeg : (Finsupp.single (1 : Fin 2) 3).degree + β.degree = k := by
      have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      simp only [map_add, Finsupp.degree_single, hs] at hadd
      simp only [Finsupp.degree_single, β]
      omega
    exact hmul ▸ Set.monomial_mul_mem_diagramSpanSet ⟨_, hv₁⟩
      (mem_diagramBox_sharpDiagram_single_one_three β) hdeg
  · by_cases hs1 : 3 ≤ s 1
    · let β : Fin 2 →₀ ℕ := s - Finsupp.single 1 3
      have hle : Finsupp.single (1 : Fin 2) 3 ≤ s := Finsupp.single_le_iff.mpr hs1
      have hmul : monomial β 1 * sharpGenerators A ⟨_, hv₂⟩ = monomial s (1 : A) := by
        simp [sharpGenerators, hne, X_pow_eq_monomial, monomial_mul_monomial, β,
          tsub_add_cancel_of_le hle]
      have hdeg : (Finsupp.single (0 : Fin 2) 3).degree + β.degree = k := by
        have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        simp only [map_add, Finsupp.degree_single, hs] at hadd
        simp only [Finsupp.degree_single, β]
        omega
      have hβ_box : β ∈ sharpDiagram.diagramBox (Finsupp.single 0 3) := by
        rw [mem_diagramBox_sharpDiagram_single_zero_three_iff]
        simp only [β, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      exact hmul ▸ Set.monomial_mul_mem_diagramSpanSet ⟨_, hv₂⟩ hβ_box hdeg
    · exact Set.monomial_mem_diagramSpanSet (by simp [sharpDiagram]; omega) hs

private theorem sharpDiagram_span_six_ne (A : Type*) [CommSemiring A] [Nontrivial A] :
    Submodule.span A (sharpDiagram.diagramSpanSet (sharpGenerators A) 6) ≠
      homogeneousSubmodule (Fin 2) A 6 := by
  intro hspan6
  have hmem6 : (X 1 ^ 6 : MvPolynomial (Fin 2) A) ∈
      Submodule.span A (sharpDiagram.diagramSpanSet (sharpGenerators A) 6) := by
    rw [hspan6, mem_homogeneousSubmodule]; exact (isHomogeneous_X A (1 : Fin 2)).pow 6
  have hker : Submodule.span A (sharpDiagram.diagramSpanSet (sharpGenerators A) 6) ≤
      LinearMap.ker (aeval (R := A) ![0, (1 : A)]).toLinearMap := by
    refine Submodule.span_le.mpr fun g hg ↦ ?_
    simp only [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    rcases hg with ⟨⟨v, hv⟩, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
    · rw [map_mul]
      rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · simp [sharpGenerators]
      · have hβ_deg : β 0 + β 1 = 3 := by
          rw [Finsupp.degree_single, Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg; omega
        have hβ1_lt : β 1 < 3 := (mem_diagramBox_sharpDiagram_single_zero_three_iff β).mp hβ
        have hle0 : Finsupp.single (0 : Fin 2) 1 ≤ β := Finsupp.single_le_iff.mpr (by omega)
        have hmul : monomial β (1 : A) = X 0 * monomial (β - Finsupp.single 0 1) 1 := by
          rw [X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle0]
        rw [hmul, map_mul]; simp
    · rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      exact False.elim (hγ (by simp [sharpDiagram]; omega))
  have hzero := hker hmem6
  simp only [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hzero
  simp at hzero

/-- Sharpness of `Set.diagramCutoff`: over any nontrivial commutative semiring `A`, there exist an
upward-closed monotone diagram `D` on `Fin 2` with `0 < D.diagramCutoff` (in fact
`D.diagramCutoff = 6` with vertices of degree `3`) and homogeneous polynomials `H` of degrees
`v.1.degree` such that `D.diagramSpanSet H k` spans `homogeneousSubmodule (Fin 2) A k` for every
`k < D.diagramCutoff`, yet `D.diagramSpanSet H D.diagramCutoff` fails to span
`homogeneousSubmodule (Fin 2) A D.diagramCutoff`. -/
theorem exists_isMonotoneDiagram_forall_lt_diagramCutoff_and_span_ne
    (A : Type*) [CommSemiring A] [Nontrivial A] :
    ∃ (D : Set (Fin 2 →₀ ℕ)) (H : D.diagramVertices → MvPolynomial (Fin 2) A),
      IsUpperSet D ∧ D.IsMonotoneDiagram ∧ (∀ v, (H v).IsHomogeneous v.1.degree) ∧
      0 < D.diagramCutoff ∧
      (∀ k < D.diagramCutoff,
        Submodule.span A (D.diagramSpanSet H k) = homogeneousSubmodule (Fin 2) A k) ∧
      Submodule.span A (D.diagramSpanSet H D.diagramCutoff) ≠
        homogeneousSubmodule (Fin 2) A D.diagramCutoff := by
  refine ⟨sharpDiagram, sharpGenerators A,
    fun _ _ hle hα ↦ hα.imp (fun h ↦ h.trans (hle 1)) (fun h ↦ h.trans (hle 0)), ?_,
    isHomogeneous_sharpGenerators A, by rw [sharpDiagram_diagramCutoff]; omega,
    fun k hk ↦ sharpDiagram_span_of_lt_six A (sharpDiagram_diagramCutoff ▸ hk),
    sharpDiagram_diagramCutoff ▸ sharpDiagram_span_six_ne A⟩
  refine Set.isMonotoneDiagram_iff.mpr fun α hα i j hij ↦ ?_
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] at hij ⊢
  · exact absurd hij (lt_irrefl _)
  · refine Or.inl ?_
    rw [Finsupp.transferExp_apply_right α (i := 0) (j := 1) (by decide)]
    rcases hα with h1 | h0 <;> omega
  · exact absurd hij (by decide)
  · exact absurd hij (lt_irrefl _)

end CutoffSharpness

end TauCeti
