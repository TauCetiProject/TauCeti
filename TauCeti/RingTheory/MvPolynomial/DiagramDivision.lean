/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Data.Finsupp.Diagram
import TauCeti.Data.Finsupp.Fin
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Bierstone–Milman's finite-degree criterion for monotone diagrams

Given a diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ`, a commutative
ring `A`, and homogeneous polynomials `H : D.diagramVertices → MvPolynomial σ A` of degrees
`v.1.degree`, Bierstone and Milman (1997, §8, pp. 274–275) define in each degree `ℓ : ℕ` the
family `D.diagramSpanSet H ℓ` of supported multiples `monomial β 1 * H v` (`β ∈ D.diagramBox v.1`,
`v.1.degree + β.degree = ℓ`) and complementary monomials `monomial γ 1` (`γ ∉ D`, `γ.degree = ℓ`).

**Theorem 8.1 (`Set.span_diagramSpanSet_eq_of_le`)** proves that if `D` is upward closed and
monotone (`D.IsMonotoneDiagram`) and `D.diagramSpanSet H k` spans `homogeneousSubmodule σ A k` at
some degree `k ≥ D.diagramCutoff`, then `D.diagramSpanSet H ℓ` spans `homogeneousSubmodule σ A ℓ`
for every `ℓ ≥ k`. We also prove boundary cases (`D = ∅`, `D = Set.univ`, and `Fin 1` cones) and
sharpness of `D.diagramCutoff` (`Set.exists_monotone_diagram_span_lt_diagramCutoff_not_span`). For
the block division endomorphism and cutoff determinant, see
`TauCeti.RingTheory.MvPolynomial.DiagramCutoffDet`.

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

private theorem homogeneousSubmodule_le_of_monomial_mem {τ R : Type*} [CommSemiring R] {ℓ : ℕ}
    {M : Submodule R (MvPolynomial τ R)}
    (h : ∀ γ : τ →₀ ℕ, γ.degree = ℓ → monomial γ 1 ∈ M) :
    homogeneousSubmodule τ R ℓ ≤ M := by
  intro p hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun γ hγ ↦ ?_
  have hdeg : γ.degree = ℓ := by
    rw [Finsupp.degree_apply]
    exact (((mem_homogeneousSubmodule ℓ p).mp hp).degree_eq_sum_deg_support hγ).symm
  have hsmul : p.coeff γ • monomial γ (1 : R) = monomial γ (p.coeff γ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  exact hsmul ▸ Submodule.smul_mem _ _ (h γ hdeg)

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

theorem diagramSpanSet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ =
      {p | ∃ γ : σ →₀ ℕ, γ.degree = ℓ ∧ p = monomial γ 1} := by
  ext p
  simp only [mem_diagramSpanSet_iff, notMem_empty, not_false_eq_true, true_and, mem_ofPred,
    or_iff_right_iff_imp]
  rintro ⟨⟨_, hv⟩, _⟩; simp at hv

/-- For `D = ∅`, the complementary monomials span every homogeneous degree independently of `H`. -/
@[simp]
theorem span_diagramSpanSet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A)
    (ℓ : ℕ) :
    Submodule.span A ((∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  refine le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule (fun ⟨_, hv⟩ ↦ by simp at hv) ℓ)
    (homogeneousSubmodule_le_of_monomial_mem fun γ hdeg ↦ ?_)
  rw [diagramSpanSet_empty]
  exact Submodule.subset_span ⟨γ, hdeg, rfl⟩

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
    · rw [zero_mul]; exact zero_mem _
  · rw [aeval_cons_zero_monomial]
    split_ifs with hγ0
    · have hγ_eq : Finsupp.cons 0 γ.tail = γ := by rw [← hγ0, Finsupp.cons_tail]
      exact Submodule.subset_span (monomial_mem_diagramSpanSet
        (fun hm ↦ hγ (hγ_eq ▸ D.mem_diagramSliceZero_iff.mp hm))
        (by simpa [hdeg] using congrArg Finsupp.degree hγ_eq))
    · exact zero_mem _

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
  have hcomp : Fin.cons (0 : MvPolynomial (Fin n) A) X ∘ Fin.succ = X := by ext i; simp
  rw [AlgHom.toLinearMap_apply, aeval_rename, hcomp, aeval_X_left, AlgHom.id_apply,
    Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨g, hg, rfl⟩
  exact aeval_cons_zero_mem_span_diagramSliceZero hD_mono hk hg

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
        monomial β' 1 * aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X) (H v) := by
      simp [Q, map_mul, aeval_cons_zero_monomial]
    rw [hkQ] at hQ_split
    rw [eq_sub_of_add_eq hQ_split]
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
      fun v' ↦ aeval (Fin.cons (0 : MvPolynomial (Fin n) A) X)
        (H ⟨Finsupp.cons 0 v'.1, mem_diagramVertices_diagramSliceZero_iff.mp v'.2⟩)
    have hH' : ∀ v', (H' v').IsHomogeneous v'.1.degree := fun v' ↦ by
      simpa [H'] using
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
      have hkP := hspan' (m + 1) (hm.trans (Nat.le_succ m))
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
    hD_up (fun j ↦ by obtain ⟨i, rfl⟩ := e.surjective j; simpa using hle i) hα
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
`constantCoeff (H ⟨0, _⟩)` is a unit in `R`. -/
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
    γ = Finsupp.single 0 γ.degree :=
  Finsupp.ext fun i ↦ by
    rw [Subsingleton.elim i 0, Finsupp.degree_eq_sum, Fintype.sum_unique, Fin.default_eq_zero,
      Finsupp.single_eq_same]

private theorem eq_monomial_single_zero_of_isHomogeneous_fin_one {d : ℕ}
    {p : MvPolynomial (Fin 1) A} (hp : p.IsHomogeneous d) :
    p = monomial (Finsupp.single 0 d) (p.coeff (Finsupp.single 0 d)) := by
  ext γ
  by_cases hγ : γ = Finsupp.single 0 d
  · subst hγ; simp
  · simp only [coeff_monomial, Ne.symm hγ, ↓reduceIte]
    refine hp.coeff_eq_zero fun hd ↦ hγ ?_
    have hdeg : γ.degree = d := by rw [Finsupp.degree_apply]; exact hd
    rw [eq_single_zero_of_fin_one γ, hdeg]

/-- In one variable (`Fin 1`), for the cone `D = Set.Ici (Finsupp.single 0 a)` and `ℓ < a`, the
complementary monomial `X 0 ^ ℓ` spans `homogeneousSubmodule (Fin 1) A ℓ` unconditionally. -/
theorem span_diagramSpanSet_Ici_single_fin_one_of_lt {a ℓ : ℕ} (hℓ : ℓ < a)
    (H : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices → MvPolynomial (Fin 1) A)
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    Submodule.span A ((Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramSpanSet H ℓ) =
      homogeneousSubmodule (Fin 1) A ℓ := by
  refine le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule hH ℓ)
    (homogeneousSubmodule_le_of_monomial_mem fun γ hdeg ↦ Submodule.subset_span
      (monomial_mem_diagramSpanSet ?_ hdeg))
  rw [eq_single_zero_of_fin_one γ, hdeg, mem_Ici, Finsupp.single_le_iff, Finsupp.single_eq_same]
  omega

/-- In one variable (`Fin 1`), for the cone `D = Set.Ici (Finsupp.single 0 a)` and `a ≤ ℓ`,
`D.diagramSpanSet H ℓ` spans `homogeneousSubmodule (Fin 1) A ℓ` if and only if the coefficient of
`X 0 ^ a` in `H ⟨Finsupp.single 0 a, _⟩` is a unit in `A`. -/
theorem span_diagramSpanSet_Ici_single_fin_one_iff {a ℓ : ℕ} (haℓ : a ≤ ℓ)
    {H : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices → MvPolynomial (Fin 1) A}
    (hH : ∀ v, (H v).IsHomogeneous v.1.degree) :
    Submodule.span A ((Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramSpanSet H ℓ) =
        homogeneousSubmodule (Fin 1) A ℓ ↔
      IsUnit ((H ⟨Finsupp.single 0 a, by simp⟩).coeff (Finsupp.single 0 a)) := by
  let v₀ : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramVertices :=
    ⟨Finsupp.single 0 a, by simp⟩
  have hv₀_eq : H v₀ = monomial (Finsupp.single 0 a) ((H v₀).coeff (Finsupp.single 0 a)) :=
    eq_monomial_single_zero_of_isHomogeneous_fin_one (by simpa [v₀] using hH v₀)
  have hmul : monomial (Finsupp.single (0 : Fin 1) (ℓ - a)) 1 * H v₀ =
      monomial (Finsupp.single 0 ℓ) ((H v₀).coeff (Finsupp.single 0 a)) := by
    conv_lhs => rw [hv₀_eq]
    rw [monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.sub_add_cancel haℓ]
  have hset : (Set.Ici (Finsupp.single (0 : Fin 1) a)).diagramSpanSet H ℓ =
      {monomial (Finsupp.single 0 ℓ) ((H v₀).coeff (Finsupp.single 0 a))} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr (hmul ▸ monomial_mul_mem_diagramSpanSet v₀
      (mem_diagramBox_iff.mpr fun α' hα' hlt ↦
        absurd ((by simpa [v₀] using hα' : α' = v₀.1) ▸ hlt) (lt_irrefl _)) ?_))
    · rintro _ (⟨⟨v, hv⟩, β, _, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
      · obtain rfl : v = Finsupp.single 0 a := by simpa using hv
        obtain rfl : β = Finsupp.single 0 (ℓ - a) := by
          rw [eq_single_zero_of_fin_one β]; rw [Finsupp.degree_single] at hdeg; congr 1; omega
        exact mem_singleton_iff.mpr hmul
      · exact False.elim (hγ (by
          rw [eq_single_zero_of_fin_one γ, hdeg, mem_Ici, Finsupp.single_le_iff,
            Finsupp.single_eq_same]
          exact haℓ))
    · change (Finsupp.single (0 : Fin 1) a).degree + (Finsupp.single 0 (ℓ - a)).degree = ℓ
      rw [Finsupp.degree_single, Finsupp.degree_single]; omega
  rw [hset, isUnit_iff_exists_inv']
  refine ⟨fun hspan ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · have hm : monomial (Finsupp.single (0 : Fin 1) ℓ) (1 : A) ∈
        Submodule.span A {monomial (Finsupp.single 0 ℓ) ((H v₀).coeff (Finsupp.single 0 a))} := by
      rw [hspan, mem_homogeneousSubmodule]
      exact isHomogeneous_monomial 1 (Finsupp.degree_single 0 ℓ)
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨u, ?_⟩
    simpa [smul_monomial] using
      congrArg (fun q : MvPolynomial (Fin 1) A ↦ q.coeff (Finsupp.single 0 ℓ)) hu
  · refine le_antisymm (hset ▸ span_diagramSpanSet_le_homogeneousSubmodule hH ℓ) fun p hp ↦ ?_
    rw [eq_monomial_single_zero_of_isHomogeneous_fin_one ((mem_homogeneousSubmodule ℓ p).mp hp),
      Submodule.mem_span_singleton]
    exact ⟨p.coeff (Finsupp.single 0 ℓ) * u, by
      rw [smul_monomial, smul_eq_mul, mul_assoc, hu, mul_one]⟩

end BoundaryCases

section CutoffSharpness

private def sharpDiagram : Set (Fin 2 →₀ ℕ) :=
  {γ | 2 ≤ γ 1 ∨ 3 ≤ γ 0}

private theorem sharpDiagram_vertices :
    sharpDiagram.diagramVertices = {Finsupp.single 1 2, Finsupp.single 0 3} := by
  ext α
  simp only [mem_diagramVertices_iff, Minimal, sharpDiagram, mem_ofPred, Finset.mem_insert,
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

private theorem fin2_eq (s : Fin 2 →₀ ℕ) : s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) := by
  ext i; fin_cases i <;> simp

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
  have hg (β : Fin 2 →₀ ℕ) (hd : (Finsupp.single (1 : Fin 2) 2).degree + β.degree = 3) :=
    Submodule.subset_span (R := ℤ) (monomial_mul_mem_diagramSpanSet (H := sharpGenerators)
      ⟨_, hv₁⟩ (mem_diagramBox_sharpDiagram_single_one_two β) hd)
  have hs_deg : s 0 + s 1 = 3 := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hs
  rw [fin2_eq s]
  rcases (by omega : s 0 = 0 ∨ s 0 = 1 ∨ s 0 = 2 ∨ s 0 = 3) with h0 | h0 | h0 | h0 <;>
    rw [h0, show s 1 = 3 - s 0 by omega] <;> simp only [h0, Nat.reduceSub, Finsupp.single_zero,
      zero_add, add_zero]
  · have hgen : monomial (0 : Fin 2 →₀ ℕ) 1 * sharpGenerators ⟨_, hv₂⟩ =
        monomial (Finsupp.single (1 : Fin 2) 3) 1 := by
      simp [sharpGenerators, hne, X_pow_eq_monomial]
    exact hgen ▸ Submodule.subset_span
      (monomial_mul_mem_diagramSpanSet ⟨_, hv₂⟩ (zero_mem_diagramBox hv₂) (by simp))
  · have heq : monomial (Finsupp.single (1 : Fin 2) 1) 1 * sharpGenerators ⟨_, hv₁⟩ -
        monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 =
        monomial (Finsupp.single 0 1 + Finsupp.single 1 2) 1 := by
      simp [sharpGenerators, mul_add, pow_two, X, monomial_mul_monomial, ← Finsupp.single_add,
        add_comm, add_left_comm]
    exact heq ▸ sub_mem (hg (Finsupp.single 1 1) (by simp)) hm21
  · exact hm21
  · have heq : monomial (Finsupp.single (0 : Fin 2) 1) 1 * sharpGenerators ⟨_, hv₁⟩ -
        monomial (Finsupp.single 0 2 + Finsupp.single 1 1) 1 = monomial (Finsupp.single 0 3) 1 := by
      simp [sharpGenerators, mul_add, pow_two, X, monomial_mul_monomial, ← add_assoc,
        ← Finsupp.single_add]
    exact heq ▸ sub_mem (hg (Finsupp.single 0 1) (by simp)) hm21

private theorem sharpDiagram_span_three :
    Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 3) =
      homogeneousSubmodule (Fin 2) ℤ 3 :=
  le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule isHomogeneous_sharpGenerators 3)
    (homogeneousSubmodule_le_of_monomial_mem fun _ hs ↦ monomial_mem_span_sharpDiagram_three hs)

private theorem sharpDiagram_span_five_ne :
    Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 5) ≠
      homogeneousSubmodule (Fin 2) ℤ 5 := by
  have hv₁ : Finsupp.single (1 : Fin 2) 2 ∈ sharpDiagram.diagramVertices := by
    rw [sharpDiagram_vertices]; simp
  intro hspan5
  have hmem5 : (X 1 ^ 5 : MvPolynomial (Fin 2) ℤ) ∈
      Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 5) := by
    rw [hspan5, mem_homogeneousSubmodule]; exact (isHomogeneous_X ℤ (1 : Fin 2)).pow 5
  have hker : Submodule.span ℤ (sharpDiagram.diagramSpanSet sharpGenerators 5) ≤
      LinearMap.ker (aeval (R := ℤ) ![0, (1 : ℤ)]).toLinearMap := by
    refine Submodule.span_le.mpr fun g hg ↦ ?_
    simp only [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    rcases hg with ⟨⟨v, hv⟩, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
    · rw [map_mul]
      rw [sharpDiagram_vertices, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · simp [sharpGenerators]
      · have hβ_deg : β 0 + β 1 = 2 := by
          rw [Finsupp.degree_single, Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg; omega
        have hlt_v : toDegLex (Finsupp.single (1 : Fin 2) 2) < toDegLex (Finsupp.single 0 3) :=
          Finsupp.DegLex.lt_iff.mpr (Or.inl (by simp))
        have hβ1_lt : β 1 < 2 := by
          by_contra! hge
          exact (mem_diagramBox_iff.mp hβ) _ hv₁ hlt_v
            (Finsupp.single_le_iff.mpr (by simpa using hge))
        have hle0 : Finsupp.single (0 : Fin 2) 1 ≤ β := Finsupp.single_le_iff.mpr (by omega)
        have hmul : monomial β (1 : ℤ) = X 0 * monomial (β - Finsupp.single 0 1) 1 := by
          rw [X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle0]
        rw [hmul, map_mul]; simp
    · rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      exact False.elim (hγ (by simp [sharpDiagram]; omega))
  have hzero := hker hmem5
  simp only [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hzero
  simp at hzero

/-- Sharpness of `Set.diagramCutoff`: in two variables (`Fin 2`), there exist an upward-closed
monotone diagram `D` whose vertices have degree at most `3` (`D.diagramCutoff = 6`) and homogeneous
polynomials `H` over `ℤ` such that `D.diagramSpanSet H 3` spans `homogeneousSubmodule (Fin 2) ℤ 3`
at `3 = max_{v ∈ D.diagramVertices} v.degree`, yet `D.diagramSpanSet H 5` fails to span
`homogeneousSubmodule (Fin 2) ℤ 5`. -/
theorem exists_monotone_diagram_span_lt_diagramCutoff_not_span :
    ∃ (D : Set (Fin 2 →₀ ℕ)) (H : D.diagramVertices → MvPolynomial (Fin 2) ℤ),
      IsUpperSet D ∧ D.IsMonotoneDiagram ∧ (∀ v, (H v).IsHomogeneous v.1.degree) ∧
      (∀ v : D.diagramVertices, v.1.degree ≤ 3) ∧
      Submodule.span ℤ (D.diagramSpanSet H 3) = homogeneousSubmodule (Fin 2) ℤ 3 ∧
      Submodule.span ℤ (D.diagramSpanSet H 5) ≠ homogeneousSubmodule (Fin 2) ℤ 5 := by
  refine ⟨sharpDiagram, sharpGenerators,
    fun _ _ hle hα ↦ hα.imp (fun h ↦ h.trans (hle 1)) (fun h ↦ h.trans (hle 0)), ?_,
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

end Set
