/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Data.Finsupp.Diagram
import TauCeti.Algebra.MvPolynomial.Rename
import TauCeti.Data.Finsupp.Fin
import TauCeti.Data.Finsupp.Order
import TauCeti.Data.Finsupp.Weight
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Bierstone–Milman's finite-degree criterion for monotone diagrams

Given a diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ`, a commutative
semiring `A`, and homogeneous polynomials `H : D.diagramVertices → MvPolynomial σ A` of degrees
`v.val.degree`, `D.diagramSpanSet H ℓ` is the degree-`ℓ` family of supported multiples
`monomial β 1 * H v` (`β ∈ D.diagramBox v.val`, `v.val.degree + β.degree = ℓ`) and complementary
monomials `monomial γ 1` (`γ ∉ D`, `γ.degree = ℓ`).

**Theorem 8.1 (`Set.span_diagramSpanSet_eq_of_le`)** proves that over a commutative ring `A`, for
upward-closed monotone `D`, spanning `homogeneousSubmodule σ A k` at some `k ≥ D.diagramCutoff`
implies spanning in every degree `ℓ ≥ k`. We also cover boundary cases (`∅`, `Set.univ`, degrees
below `D`, and `Set.Ici α` in one variable) and sharpness of `Set.diagramCutoff`
(`TauCeti.exists_isMonotoneDiagram_forall_lt_diagramCutoff_and_span_ne`). For the block division
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
      β ∈ D.diagramBox v.val ∧ v.val.degree + β.degree = ℓ ∧ p = monomial β 1 * H v} ∪
    {p | ∃ γ ∉ D, γ.degree = ℓ ∧ p = monomial γ 1}

theorem mem_diagramSpanSet_iff {D : Set (σ →₀ ℕ)} {H : D.diagramVertices → MvPolynomial σ A}
    {ℓ : ℕ} {p : MvPolynomial σ A} : p ∈ D.diagramSpanSet H ℓ ↔
      (∃ (v : D.diagramVertices) (β : σ →₀ ℕ), β ∈ D.diagramBox v.val ∧
        v.val.degree + β.degree = ℓ ∧ p = monomial β 1 * H v) ∨
      (∃ γ ∉ D, γ.degree = ℓ ∧ p = monomial γ 1) := Iff.rfl

theorem monomial_mul_mem_diagramSpanSet {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} {ℓ : ℕ} (v : D.diagramVertices) {β : σ →₀ ℕ}
    (hβ : β ∈ D.diagramBox v.val) (hdeg : v.val.degree + β.degree = ℓ) :
    monomial β 1 * H v ∈ D.diagramSpanSet H ℓ := Or.inl ⟨v, β, hβ, hdeg, rfl⟩

theorem monomial_mem_diagramSpanSet {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} {ℓ : ℕ} {γ : σ →₀ ℕ} (hγ : γ ∉ D)
    (hdeg : γ.degree = ℓ) : monomial γ 1 ∈ D.diagramSpanSet H ℓ := Or.inr ⟨γ, hγ, hdeg, rfl⟩

theorem isHomogeneous_of_mem_diagramSpanSet {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {ℓ : ℕ} {p : MvPolynomial σ A} (hp : p ∈ D.diagramSpanSet H ℓ) : p.IsHomogeneous ℓ := by
  rcases hp with ⟨v, β, _, rfl, rfl⟩ | ⟨γ, _, rfl, rfl⟩
  exacts [add_comm β.degree v.val.degree ▸ (isHomogeneous_monomial 1 (by simp)).mul (hH v),
    isHomogeneous_monomial 1 (by simp)]

theorem span_diagramSpanSet_le_homogeneousSubmodule {D : Set (σ →₀ ℕ)}
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    (ℓ : ℕ) : Submodule.span A (D.diagramSpanSet H ℓ) ≤ homogeneousSubmodule σ A ℓ :=
  Submodule.span_le.mpr fun _ hp ↦ (mem_homogeneousSubmodule ℓ _).mpr
    (isHomogeneous_of_mem_diagramSpanSet hH hp)

/-- Relabeling variables along an order isomorphism `e : τ ≃o σ` transports `diagramSpanSet`. -/
theorem image_renameEquiv_diagramSpanSet {τ : Type*} [Finite τ] [LinearOrder τ] (e : τ ≃o σ)
    (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (renameEquiv A e.toEquiv) ''
        ((Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramSpanSet
          (fun v₀ ↦ (renameEquiv A e.toEquiv).symm
            (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.val,
              (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.property⟩)) ℓ) =
      D.diagramSpanSet H ℓ := by
  have hren (s : τ →₀ ℕ) : renameEquiv A e.toEquiv (monomial s (1 : A)) =
      monomial (Finsupp.equivMapDomain e.toEquiv s) 1 := by
    rw [renameEquiv_apply, rename_monomial, Finsupp.equivMapDomain_eq_mapDomain]
  have hsurj := (Finsupp.domCongr e.toEquiv (M := ℕ)).surjective
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨q, (⟨v₀, β₀, hβ₀, hdeg₀, rfl⟩ | ⟨γ₀, hγ₀, hdeg₀, rfl⟩), rfl⟩
    · rw [map_mul, AlgEquiv.apply_symm_apply, hren]; exact monomial_mul_mem_diagramSpanSet ⟨_, _⟩
        ((mem_diagramBox_preimage_equivMapDomain_iff e).mp hβ₀)
        (by simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg₀)
    · rw [hren]; exact monomial_mem_diagramSpanSet hγ₀
        (by simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg₀)
  · rintro _ (⟨⟨v, hv⟩, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
    · obtain ⟨v₀, rfl⟩ := hsurj v; obtain ⟨β₀, rfl⟩ := hsurj β
      exact ⟨_, monomial_mul_mem_diagramSpanSet ⟨v₀,
        (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mpr hv⟩
        ((mem_diagramBox_preimage_equivMapDomain_iff e).mpr hβ)
        (by simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg),
        by rw [map_mul, AlgEquiv.apply_symm_apply, hren]; rfl⟩
    · obtain ⟨γ₀, rfl⟩ := hsurj γ; exact ⟨_, monomial_mem_diagramSpanSet hγ
        (by simpa [Finsupp.equivMapDomain_eq_mapDomain] using hdeg), hren γ₀⟩

/-- If every element of `D` has degree strictly greater than `ℓ`, then `D.diagramSpanSet H ℓ`
consists precisely of all monomials of degree `ℓ` (independently of `H`). -/
theorem diagramSpanSet_of_forall_lt_degree {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (hD : ∀ γ ∈ D, ℓ < γ.degree) (H : D.diagramVertices → MvPolynomial σ A) :
    D.diagramSpanSet H ℓ = {p | ∃ γ : σ →₀ ℕ, γ.degree = ℓ ∧ p = monomial γ 1} := by
  ext p; simp only [mem_diagramSpanSet_iff, mem_ofPred]
  exact ⟨fun h ↦ h.elim (fun ⟨v, _⟩ ↦ absurd (hD v.val (D.diagramVertices_subset v.property))
      (by omega)) (fun ⟨γ, _, h⟩ ↦ ⟨γ, h⟩),
    fun ⟨γ, hdeg, hp⟩ ↦ Or.inr ⟨γ, fun hm ↦ (hD γ hm).ne' hdeg, hdeg, hp⟩⟩

/-- If every element of `D` has degree strictly greater than `ℓ`, then `D.diagramSpanSet H ℓ`
spans `homogeneousSubmodule σ A ℓ` independently of `H`. -/
theorem span_diagramSpanSet_of_forall_lt_degree {D : Set (σ →₀ ℕ)} {ℓ : ℕ}
    (hD : ∀ γ ∈ D, ℓ < γ.degree) (H : D.diagramVertices → MvPolynomial σ A) :
    Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ := by
  rw [diagramSpanSet_of_forall_lt_degree hD]; exact le_antisymm (Submodule.span_le.mpr fun _
    ⟨_, hdeg, hp⟩ ↦ hp ▸ (mem_homogeneousSubmodule ℓ _).mpr (isHomogeneous_monomial 1 hdeg))
    (homogeneousSubmodule_le_iff.mpr fun γ hdeg ↦ Submodule.subset_span ⟨γ, hdeg, rfl⟩)

theorem diagramSpanSet_empty (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ = {p | ∃ γ : σ →₀ ℕ, γ.degree = ℓ ∧ p = monomial γ 1} :=
  diagramSpanSet_of_forall_lt_degree (fun _ ↦ False.elim) H

/-- For `D = ∅`, the complementary monomials span every homogeneous degree independently of `H`. -/
@[simp] theorem span_diagramSpanSet_empty
    (H : (∅ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    Submodule.span A ((∅ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  span_diagramSpanSet_of_forall_lt_degree (fun _ ↦ False.elim) H

end SpanSet

section FiniteDegreeCriterion

variable {A : Type*} [CommRing A]

private noncomputable def sliceGenerators {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A) :
    D.diagramSliceZero.diagramVertices → MvPolynomial (Fin n) A := fun v' ↦
  (H ⟨Finsupp.cons 0 v'.val, mem_diagramVertices_diagramSliceZero_iff.mp v'.property⟩).killCompl
    (Fin.succ_injective n)

private theorem killCompl_eq_sliceGenerators {n : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A)
    {v : D.diagramVertices} (hv0 : v.val 0 = 0) :
    (H v).killCompl (Fin.succ_injective n) =
      sliceGenerators H ⟨v.val.tail,
        mem_diagramVertices_diagramSliceZero_iff.mpr
          (Finsupp.cons_zero_tail hv0 ▸ v.property)⟩ := by
  simp only [sliceGenerators]
  congr 2
  exact Subtype.ext (Finsupp.cons_zero_tail hv0).symm

private theorem X_zero_mul_mem_span_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A} (hm : D.diagramCutoff ≤ m)
    (hspan_m : homogeneousSubmodule (Fin (n + 1)) A m ≤ Submodule.span A (D.diagramSpanSet H m))
    {Q : MvPolynomial (Fin (n + 1)) A} (hQ : Q.IsHomogeneous m) :
    X 0 * Q ∈ Submodule.span A (D.diagramSpanSet H (m + 1)) :=
  (Submodule.image_span_subset (LinearMap.mulLeft A (X 0)) _ _).mpr (fun _ hg ↦
    Submodule.subset_span <| by
      rw [LinearMap.mulLeft_apply]; rcases hg with ⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
      · rw [← mul_assoc, X, monomial_mul_monomial, mul_one]; exact monomial_mul_mem_diagramSpanSet v
          (single_zero_add_mem_diagramBox hD_mono hβ (hdeg ▸ hm))
          (by simp [Finsupp.degree_single]; omega)
      · rw [X, monomial_mul_monomial, mul_one]; exact monomial_mem_diagramSpanSet
          (single_zero_add_notMem_of_notMem hD_up hD_mono hγ (hdeg ▸ hm))
          (by simp [hdeg, add_comm])) ⟨Q, hspan_m ((mem_homogeneousSubmodule m Q).mpr hQ), rfl⟩

private theorem span_diagramSliceZero_of_span {n k : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_mono : D.IsMonotoneDiagram) {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A}
    (hk : D.diagramCutoff ≤ k)
    (hspan : homogeneousSubmodule (Fin (n + 1)) A k ≤ Submodule.span A (D.diagramSpanSet H k)) :
    homogeneousSubmodule (Fin n) A k ≤
      Submodule.span A (D.diagramSliceZero.diagramSpanSet (sliceGenerators H) k) := by
  intro q hq
  -- Push `rename Fin.succ q` through `killCompl (Fin.succ_injective n)` along `hspan`.
  have hrename : rename Fin.succ q ∈ Submodule.span A (D.diagramSpanSet H k) :=
    hspan ((mem_homogeneousSubmodule k _).mpr
      ((IsHomogeneous.rename_isHomogeneous_iff (Fin.succ_injective n)).mpr
        ((mem_homogeneousSubmodule k q).mp hq)))
  have himg := (Submodule.image_span_subset
    (killCompl (R := A) (Fin.succ_injective n)).toLinearMap
    (D.diagramSpanSet H k)
    (Submodule.span A (D.diagramSliceZero.diagramSpanSet (sliceGenerators H) k))).mpr ?_
  · simpa using himg ⟨rename Fin.succ q, hrename, rfl⟩
  · intro _ hg
    simp only [AlgHom.toLinearMap_apply]
    have hkill0 {α : Fin (n + 1) →₀ ℕ} (h : α 0 ≠ 0) :
        (monomial α (1 : A)).killCompl (Fin.succ_injective n) = 0 :=
      killCompl_monomial_eq_zero_of_notMem_range _ _ (Finsupp.mem_support_iff.mpr h) (by simp)
    rcases hg with ⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
    · rw [map_mul]
      by_cases hβ0 : β 0 = 0
      · rw [killCompl_monomial_of_apply_zero hβ0]
        by_cases hv0 : v.val 0 = 0
        · -- Both `v` and `β` avoid variable `0`, so the term projects to `sliceGenerators`.
          rw [killCompl_eq_sliceGenerators H hv0]
          have hv' : v.val.tail ∈ D.diagramSliceZero.diagramVertices :=
            mem_diagramVertices_diagramSliceZero_iff.mpr (Finsupp.cons_zero_tail hv0 ▸ v.property)
          have hβ' : β.tail ∈ D.diagramSliceZero.diagramBox v.val.tail :=
            cons_zero_mem_diagramBox_iff.mp
              (by simpa [Finsupp.cons_zero_tail hv0, Finsupp.cons_zero_tail hβ0] using hβ)
          have hdeg' : v.val.tail.degree + β.tail.degree = k := by
            rw [Finsupp.degree_tail_of_apply_zero hv0, Finsupp.degree_tail_of_apply_zero hβ0, hdeg]
          exact Submodule.subset_span (monomial_mul_mem_diagramSpanSet ⟨v.val.tail, hv'⟩ hβ' hdeg')
        · -- When `1 ≤ v 0` and `β 0 = 0`, the degree bound forces `v.degree + β.degree < k`.
          exact absurd (degree_add_lt_diagramCutoff_of_mem_diagramBox hD_mono v.property
            (Nat.pos_of_ne_zero hv0) hβ hβ0) (by omega)
      · -- Monomials involving variable `0` are killed by `killCompl`.
        rw [hkill0 hβ0, zero_mul]
        exact zero_mem _
    · by_cases hγ0 : γ 0 = 0
      · -- Remainder monomials avoiding variable `0` project to remainders outside the slice.
        rw [killCompl_monomial_of_apply_zero hγ0]
        exact Submodule.subset_span
          (monomial_mem_diagramSpanSet (fun hm ↦ hγ
            (Finsupp.cons_zero_tail hγ0 ▸ D.mem_diagramSliceZero_iff.mp hm))
            ((Finsupp.degree_tail_of_apply_zero hγ0).trans hdeg))
      · -- Remainder monomials involving variable `0` are killed by `killCompl`.
        rw [hkill0 hγ0]
        exact zero_mem _

private theorem rename_succ_mem_span_diagramSpanSet {n m : ℕ} {D : Set (Fin (n + 1) →₀ ℕ)}
    (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial (Fin (n + 1)) A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) (hm : D.diagramCutoff ≤ m)
    (ihm : homogeneousSubmodule (Fin (n + 1)) A m ≤ Submodule.span A (D.diagramSpanSet H m))
    {g' : MvPolynomial (Fin n) A}
    (hg' : g' ∈ D.diagramSliceZero.diagramSpanSet (sliceGenerators H) (m + 1)) :
    rename Fin.succ g' ∈ Submodule.span A (D.diagramSpanSet H (m + 1)) := by
  rcases hg' with ⟨v', β', hβ', hdeg', rfl⟩ | ⟨γ', hγ', hdeg', rfl⟩
  · have hQ : monomial (Finsupp.cons 0 β') 1 * H ⟨Finsupp.cons 0 v'.val,
        mem_diagramVertices_diagramSliceZero_iff.mp v'.property⟩ ∈ D.diagramSpanSet H (m + 1) :=
      monomial_mul_mem_diagramSpanSet _ (cons_zero_mem_diagramBox_iff.mpr hβ') (by simpa)
    obtain ⟨R, hR, hsplit⟩ :=
      (isHomogeneous_of_mem_diagramSpanSet hH hQ).exists_eq_rename_succ_add_X_zero_mul
    conv_rhs at hsplit => rw [map_mul, ← Finsupp.mapDomain_finSucc, killCompl_monomial_mapDomain]
    exact eq_sub_of_add_eq hsplit.symm ▸ sub_mem (Submodule.subset_span hQ)
      (X_zero_mul_mem_span_diagramSpanSet hD_up hD_mono hm ihm hR)
  · rw [rename_monomial, Finsupp.mapDomain_finSucc]; exact Submodule.subset_span
      (monomial_mem_diagramSpanSet (mt D.mem_diagramSliceZero_iff.mpr hγ') (by simpa using hdeg'))

private theorem homogeneousSubmodule_le_span_fin :
    ∀ {d : ℕ} {D : Set (Fin d →₀ ℕ)} (_hD_up : IsUpperSet D) (_hD_mono : D.IsMonotoneDiagram)
      {H : D.diagramVertices → MvPolynomial (Fin d) A}
      (_hH : ∀ v, (H v).IsHomogeneous v.val.degree) {k : ℕ} (_hk : D.diagramCutoff ≤ k)
      (_hspan : homogeneousSubmodule (Fin d) A k ≤ Submodule.span A (D.diagramSpanSet H k))
      {ℓ : ℕ} (_hℓ : k ≤ ℓ),
      homogeneousSubmodule (Fin d) A ℓ ≤ Submodule.span A (D.diagramSpanSet H ℓ)
  | 0, _, _, _, _, _, _, _, hspan, _, hℓ => hℓ.eq_or_lt.elim (fun h ↦ h ▸ hspan) fun hlt ↦ by
    obtain ⟨_, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hlt)
    rw [MvPolynomial.homogeneousSubmodule_succ_eq_bot_of_isEmpty]; exact bot_le
  | n + 1, D, hD_up, hD_mono, H, hH, k, hk, hspan, ℓ, hℓ => by
    induction ℓ, hℓ using Nat.le_induction with
    | base => exact hspan
    | succ m hm ihm =>
      intro P hP; obtain ⟨Q, hQ, hsplit⟩ :=
        ((mem_homogeneousSubmodule (m + 1) P).mp hP).exists_eq_rename_succ_add_X_zero_mul
      have hH' : ∀ v', (sliceGenerators H v').IsHomogeneous v'.val.degree := fun v' ↦ by
        simpa [sliceGenerators] using (hH ⟨_, mem_diagramVertices_diagramSliceZero_iff.mp
          v'.property⟩).killCompl (Fin.succ_injective n)
      exact hsplit ▸ add_mem ((Submodule.image_span_subset (rename (R := A) Fin.succ).toLinearMap
        _ _).mpr (fun _ ↦ rename_succ_mem_span_diagramSpanSet hD_up hD_mono hH (hk.trans hm) ihm)
        ⟨P.killCompl (Fin.succ_injective n), homogeneousSubmodule_le_span_fin hD_up.diagramSliceZero
          hD_mono.diagramSliceZero hH' ((diagramCutoff_diagramSliceZero_le D).trans hk)
          (span_diagramSliceZero_of_span hD_mono hk hspan) (hm.trans (Nat.le_succ m))
          ((mem_homogeneousSubmodule (m + 1) _).mpr (((mem_homogeneousSubmodule (m + 1) P).mp hP
            ).killCompl (Fin.succ_injective n))), rfl⟩)
        (X_zero_mul_mem_span_diagramSpanSet hD_up hD_mono (hk.trans hm) ihm hQ)

private theorem homogeneousSubmodule_le_span_preimage_equivMapDomain_iff
    {σ τ : Type*} [Finite σ] [LinearOrder σ] [Finite τ] [LinearOrder τ] (e : τ ≃o σ)
    (D : Set (σ →₀ ℕ)) (H : D.diagramVertices → MvPolynomial σ A) (m : ℕ) :
    homogeneousSubmodule τ A m ≤
        Submodule.span A ((Finsupp.equivMapDomain e.toEquiv ⁻¹' D).diagramSpanSet
          (fun v₀ ↦ (renameEquiv A e.toEquiv).symm
            (H ⟨Finsupp.equivMapDomain e.toEquiv v₀.val,
              (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.property⟩)) m) ↔
      homogeneousSubmodule σ A m ≤ Submodule.span A (D.diagramSpanSet H m) := by
  let g := renameEquiv A e.toEquiv
  have hmap := (congrArg (Submodule.span A)
    (image_renameEquiv_diagramSpanSet e D H m).symm).trans (Submodule.map_span g.toLinearMap _).symm
  have hhom {q} : q ∈ homogeneousSubmodule τ A m ↔ g q ∈ homogeneousSubmodule σ A m := by
    simpa [mem_homogeneousSubmodule, g, renameEquiv_apply] using
      (IsHomogeneous.rename_isHomogeneous_iff e.injective).symm
  refine ⟨fun hle p hp ↦ ?_, fun hle q hq ↦ ?_⟩
  · have hmem := Submodule.mem_map_of_mem (f := g.toLinearMap)
      (hle ((hhom (q := g.symm p)).mpr (by rwa [g.apply_symm_apply])))
    rwa [AlgEquiv.toLinearMap_apply, g.apply_symm_apply, ← hmap] at hmem
  · obtain ⟨q', hq', heq⟩ := Submodule.mem_map.mp (hmap ▸ hle (hhom.mp hq))
    rwa [g.injective heq] at hq'

/-- **Bierstone–Milman's Finite-Degree Criterion** (inclusion form, Theorem 8.1): for an
upward-closed monotone diagram `D` on a finite linearly ordered variable set `σ`, if
`D.diagramSpanSet H k` spans `homogeneousSubmodule σ A k` at some `k ≥ D.diagramCutoff`, then it
spans `homogeneousSubmodule σ A ℓ` for every `ℓ ≥ k`. -/
theorem homogeneousSubmodule_le_span_diagramSpanSet_of_le {σ : Type*} [Finite σ] [LinearOrder σ]
    {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {k : ℕ} (hk : D.diagramCutoff ≤ k)
    (hspan : homogeneousSubmodule σ A k ≤ Submodule.span A (D.diagramSpanSet H k))
    {ℓ : ℕ} (hℓ : k ≤ ℓ) :
    homogeneousSubmodule σ A ℓ ≤ Submodule.span A (D.diagramSpanSet H ℓ) := by
  cases nonempty_fintype σ; let e : Fin (Fintype.card σ) ≃o σ := Fintype.orderIsoFinOfCardEq σ rfl
  refine (homogeneousSubmodule_le_span_preimage_equivMapDomain_iff e D H ℓ).mp
    (homogeneousSubmodule_le_span_fin (fun _ _ hle hα ↦ hD_up (by simpa using hle) hα)
      ((isMonotoneDiagram_preimage_equivMapDomain e).mpr hD_mono) (fun v₀ ↦
        (IsHomogeneous.rename_isHomogeneous_iff e.symm.injective).mpr <| by
          simpa [renameEquiv_symm, renameEquiv_apply, Finsupp.equivMapDomain_eq_mapDomain] using
            hH ⟨Finsupp.equivMapDomain e.toEquiv v₀.val,
              (mem_diagramVertices_preimage_equivMapDomain_iff e.toEquiv).mp v₀.property⟩)
      (by rwa [diagramCutoff_preimage_equivMapDomain e D])
      ((homogeneousSubmodule_le_span_preimage_equivMapDomain_iff e D H k).mpr hspan) hℓ)

/-- **Bierstone–Milman's Finite-Degree Criterion** (Theorem 8.1): for an upward-closed monotone
diagram `D : Set (σ →₀ ℕ)` on a finite linearly ordered variable set `σ` and homogeneous
polynomials `H v` of degree `v.val.degree` over a commutative ring `A`, if
`Submodule.span A (D.diagramSpanSet H k) = homogeneousSubmodule σ A k` at some
`k ≥ D.diagramCutoff`, then `Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ`
for every `ℓ ≥ k`. -/
theorem span_diagramSpanSet_eq_of_le {σ : Type*} [Finite σ] [LinearOrder σ]
    {D : Set (σ →₀ ℕ)} (hD_up : IsUpperSet D) (hD_mono : D.IsMonotoneDiagram)
    {H : D.diagramVertices → MvPolynomial σ A} (hH : ∀ v, (H v).IsHomogeneous v.val.degree)
    {k : ℕ} (hk : D.diagramCutoff ≤ k)
    (hspan : Submodule.span A (D.diagramSpanSet H k) = homogeneousSubmodule σ A k)
    {ℓ : ℕ} (hℓ : k ≤ ℓ) : Submodule.span A (D.diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule hH ℓ)
    (homogeneousSubmodule_le_span_diagramSpanSet_of_le hD_up hD_mono hH hk hspan.ge hℓ)

end FiniteDegreeCriterion

section BoundaryCases

variable {σ A : Type*} [CommSemiring A] [Finite σ] [LinearOrder σ]

/-- For `D = Set.univ`, `D.diagramSpanSet H ℓ` consists precisely of the multiples
`monomial β 1 * H ⟨0, _⟩` with `β.degree = ℓ`. -/
theorem diagramSpanSet_univ
    (H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A) (ℓ : ℕ) :
    (Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ =
      {p | ∃ β : σ →₀ ℕ, β.degree = ℓ ∧ p = monomial β 1 * H ⟨0, by simp⟩} := by
  ext p; simp only [mem_diagramSpanSet_iff, mem_univ, not_true_eq_false, false_and, exists_false,
    or_false, mem_ofPred]
  exact ⟨fun ⟨v, β, _, hdeg, hp⟩ ↦ ⟨β, by simpa [show v.val = 0 by simpa using v.property]
      using hdeg, (Subtype.ext (by simpa using v.property) : v = ⟨0, by simp⟩) ▸ hp⟩,
    fun ⟨β, hdeg, hp⟩ ↦ ⟨⟨0, by simp⟩, β, by simp, by simpa using hdeg, hp⟩⟩

/-- For `D = Set.univ` (the quadrant of the vertex `0`), spanning in degree `0` holds if and only
if the constant coefficient of `H ⟨0, _⟩` is a unit in `A`. -/
theorem span_diagramSpanSet_univ_zero_iff
    {H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    Submodule.span A ((Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H 0) =
        homogeneousSubmodule σ A 0 ↔ IsUnit (constantCoeff (H ⟨0, by simp⟩)) := by
  let v₀ : (Set.univ : Set (σ →₀ ℕ)).diagramVertices := ⟨0, by simp⟩
  have hv₀ := IsHomogeneous.eq_C_constantCoeff (by simpa [v₀] using hH v₀)
  have hset : (Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H 0 = {H v₀} := by
    rw [diagramSpanSet_univ]; ext p; simp [v₀, Finsupp.degree_eq_zero_iff]
  rw [hset, hv₀, isUnit_iff_exists_inv']; refine ⟨fun hspan ↦ ?_, fun ⟨a, ha⟩ ↦ le_antisymm
    (hv₀ ▸ hset ▸ span_diagramSpanSet_le_homogeneousSubmodule hH 0) fun p hp ↦
      Submodule.mem_span_singleton.mpr ⟨constantCoeff p * a, by rw [constantCoeff_C] at ha; rw
        [smul_eq_C_mul, ← map_mul, mul_assoc, ha, mul_one,
          ← IsHomogeneous.eq_C_constantCoeff ((mem_homogeneousSubmodule 0 p).mp hp)]⟩⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (hspan.symm ▸ (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_one σ A))
  exact ⟨a, by simpa [smul_eq_C_mul] using congrArg constantCoeff ha⟩

/-- For `D = Set.univ`, `D.diagramSpanSet H ℓ` spans in *all* degrees `ℓ : ℕ` if and only if
`constantCoeff (H ⟨0, _⟩)` is a unit in `A`. -/
theorem forall_span_diagramSpanSet_univ_iff
    {H : (Set.univ : Set (σ →₀ ℕ)).diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (∀ ℓ : ℕ, Submodule.span A ((Set.univ : Set (σ →₀ ℕ)).diagramSpanSet H ℓ) =
        homogeneousSubmodule σ A ℓ) ↔ IsUnit (constantCoeff (H ⟨0, by simp⟩)) := by
  refine ⟨fun h ↦ (span_diagramSpanSet_univ_zero_iff hH).mp (h 0), fun hu ℓ ↦ ?_⟩
  let v₀ : (Set.univ : Set (σ →₀ ℕ)).diagramVertices := ⟨0, by simp⟩
  have hv₀ := IsHomogeneous.eq_C_constantCoeff (by simpa [v₀] using hH v₀)
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv'.mp hu
  exact le_antisymm (span_diagramSpanSet_le_homogeneousSubmodule hH ℓ)
    (homogeneousSubmodule_le_iff.mpr fun γ hdeg ↦ (show a • (monomial γ 1 * H v₀) = monomial γ 1
      by rw [hv₀, smul_eq_C_mul, mul_left_comm, ← map_mul, ha, C_1, mul_one]) ▸ Submodule.smul_mem
      _ a (Submodule.subset_span (monomial_mul_mem_diagramSpanSet v₀ (by simp [v₀])
        (by simp [v₀, hdeg]))))

/-- For any principal cone `Set.Ici α` and degree `ℓ < α.degree`, `diagramSpanSet` spans
`homogeneousSubmodule σ A ℓ` unconditionally (independently of `H`). -/
theorem span_diagramSpanSet_Ici_of_lt {α : σ →₀ ℕ} {ℓ : ℕ} (hℓ : ℓ < α.degree)
    (H : (Set.Ici α).diagramVertices → MvPolynomial σ A) :
    Submodule.span A ((Set.Ici α).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ :=
  span_diagramSpanSet_of_forall_lt_degree (fun _ hγ ↦ lt_of_lt_of_le hℓ (Finsupp.degree_mono hγ)) H

/-- In a single variable (`[Unique σ]`), for the cone `D = Set.Ici α` and `α.degree ≤ ℓ`,
`D.diagramSpanSet H ℓ` is the singleton
`{monomial (Finsupp.single default ℓ) ((H ⟨α, _⟩).coeff α)}`. -/
theorem diagramSpanSet_Ici [Unique σ] {α : σ →₀ ℕ} {ℓ : ℕ} (haℓ : α.degree ≤ ℓ)
    {H : (Set.Ici α).diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    (Set.Ici α).diagramSpanSet H ℓ =
      {monomial (Finsupp.single (default : σ) ℓ) ((H ⟨α, by simp⟩).coeff α)} := by
  let v₀ : (Set.Ici α).diagramVertices := ⟨α, by simp⟩
  have hmul : monomial (Finsupp.single (default : σ) (ℓ - α.degree)) 1 * H v₀ =
      monomial (Finsupp.single default ℓ) ((H v₀).coeff α) := by
    nth_rw 1 [show H v₀ = monomial (Finsupp.single (default : σ) α.degree) ((H v₀).coeff α) by
      simpa only [v₀, ← Finsupp.unique_single_degree α] using (hH v₀).eq_monomial_single_default]
    rw [monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.sub_add_cancel haℓ]
  refine Subset.antisymm ?_ (singleton_subset_iff.mpr (hmul ▸ monomial_mul_mem_diagramSpanSet v₀
    (by simp [v₀]) (by dsimp only [v₀]; rw [Finsupp.degree_single]; omega)))
  rintro _ (⟨v, β, _, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩)
  · obtain rfl : v = v₀ := Subtype.ext (by simpa [v₀] using v.property)
    obtain rfl : β = Finsupp.single default (ℓ - α.degree) := by
      rw [Finsupp.unique_single_degree β]; dsimp only [v₀] at hdeg; congr 1; omega
    exact hmul
  · exact (hγ (by rw [Set.mem_Ici, Finsupp.unique_single_degree α,
      Finsupp.unique_single_degree γ, hdeg]; simpa [Finsupp.single_le_iff] using haℓ)).elim

/-- In a single variable (`[Unique σ]`), for the cone `D = Set.Ici α` and `α.degree ≤ ℓ`,
`D.diagramSpanSet H ℓ` spans `homogeneousSubmodule σ A ℓ` if and only if `(H ⟨α, _⟩).coeff α` is
a unit in `A`. -/
theorem span_diagramSpanSet_Ici_iff [Unique σ] {α : σ →₀ ℕ} {ℓ : ℕ} (haℓ : α.degree ≤ ℓ)
    {H : (Set.Ici α).diagramVertices → MvPolynomial σ A}
    (hH : ∀ v, (H v).IsHomogeneous v.val.degree) :
    Submodule.span A ((Set.Ici α).diagramSpanSet H ℓ) = homogeneousSubmodule σ A ℓ ↔
      IsUnit ((H ⟨α, by simp⟩).coeff α) := by
  have hset := diagramSpanSet_Ici haℓ hH; rw [hset, isUnit_iff_exists_inv']
  refine ⟨fun hspan ↦ ?_, fun ⟨u, hu⟩ ↦ le_antisymm
    (hset ▸ span_diagramSpanSet_le_homogeneousSubmodule hH ℓ) fun p hp ↦ ?_⟩
  · obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp
      (hspan.symm ▸ (mem_homogeneousSubmodule ℓ _).mpr
        (isHomogeneous_monomial 1 (Finsupp.degree_single (default : σ) ℓ)))
    exact ⟨u, by simpa [smul_monomial] using
      (congrArg (fun q : MvPolynomial σ A ↦ q.coeff (Finsupp.single default ℓ)) hu)⟩
  · rw [((mem_homogeneousSubmodule ℓ p).mp hp).eq_monomial_single_default,
      Submodule.mem_span_singleton]
    exact ⟨p.coeff (Finsupp.single default ℓ) * u,
      by rw [smul_monomial, smul_eq_mul, mul_assoc, hu, mul_one]⟩

end BoundaryCases

end Set

namespace TauCeti

section CutoffSharpness

private def sharpDiagram : Set (Fin 2 →₀ ℕ) := {γ | 3 ≤ γ 1 ∨ 3 ≤ γ 0}

private theorem sharpDiagram_vertices :
    sharpDiagram.diagramVertices = {Finsupp.single 1 3, Finsupp.single 0 3} := by
  have hle {α : Fin 2 →₀ ℕ} {i : Fin 2} (h : 3 ≤ α i) := Finsupp.single_le_iff.mpr h
  ext α; simp only [Set.mem_diagramVertices_iff, Minimal, sharpDiagram, Set.mem_ofPred,
    Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun ⟨h, hm⟩ ↦ h.imp (fun h1 ↦ le_antisymm (hm (Or.inl (by simp)) (hle h1)) (hle h1))
      (fun h0 ↦ le_antisymm (hm (Or.inr (by simp)) (hle h0)) (hle h0)),
    fun h ↦ h.elim (fun h ↦ h ▸ ⟨Or.inl (by simp), fun _ g l ↦ hle (g.resolve_right
        (by have := l 0; simp at this; omega))⟩) (fun h ↦ h ▸ ⟨Or.inr (by simp), fun _ g l ↦ hle
        (g.resolve_left (by have := l 1; simp at this; omega))⟩)⟩

private theorem toDegLex_sharpDiagram_lt :
    toDegLex (Finsupp.single (1 : Fin 2) 3) < toDegLex (Finsupp.single 0 3) :=
  Finsupp.DegLex.lt_iff.mpr <| Or.inr ⟨by simp,
    Finsupp.Lex.lt_iff.mpr ⟨0, fun _ h ↦ absurd h (Fin.not_lt_zero _), by simp⟩⟩

open scoped Classical in
private noncomputable def sharpGenerators (A : Type*) [CommSemiring A] :
    sharpDiagram.diagramVertices → MvPolynomial (Fin 2) A :=
  fun v ↦ if v.val = Finsupp.single 1 3 then X 0 ^ 3 else X 1 ^ 3

private theorem mem_diagramBox_sharpDiagram_single_zero_three_iff (β : Fin 2 →₀ ℕ) :
    β ∈ sharpDiagram.diagramBox (Finsupp.single 0 3) ↔ β 1 < 3 := by
  simp only [Set.mem_diagramBox_iff, sharpDiagram_vertices, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq, lt_self_iff_false, IsEmpty.forall_iff,
    and_true, toDegLex_sharpDiagram_lt, true_imp_iff, Finsupp.single_le_iff, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_add, not_le]

private theorem isUpperSet_sharpDiagram : IsUpperSet sharpDiagram :=
  fun _ _ hle hα ↦ hα.imp (fun h ↦ h.trans (hle 1)) (fun h ↦ h.trans (hle 0))

private theorem isMonotoneDiagram_sharpDiagram : sharpDiagram.IsMonotoneDiagram := by
  refine Set.isMonotoneDiagram_iff.mpr fun α hα i j hij ↦ Or.inl ?_
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 1 := ⟨by omega, by omega⟩
  rw [Finsupp.transferExp_apply_right α (by decide)]
  rcases hα with h1 | h0 <;> omega

private theorem diagramCutoff_sharpDiagram : sharpDiagram.diagramCutoff = 6 := by
  have hs0 : sharpDiagram.diagramSliceZero = Set.Ici (Finsupp.single (0 : Fin 1) 3) := by
    ext γ'
    simp only [Set.mem_diagramSliceZero_iff, sharpDiagram, Set.mem_ofPred, Finsupp.cons_zero,
      Set.mem_Ici, Finsupp.single_le_iff]
    exact ⟨fun h ↦ h.resolve_right (by decide), Or.inl⟩
  rw [Set.diagramCutoff_fin_succ, hs0, Set.diagramCutoff_fin_succ, Set.diagramVertices_Ici,
    sharpDiagram_vertices]
  simp [Finset.filter_insert, Finset.filter_singleton]

private theorem isHomogeneous_sharpGenerators (A : Type*) [CommSemiring A]
    (v : sharpDiagram.diagramVertices) : (sharpGenerators A v).IsHomogeneous v.val.degree := by
  rcases (by simpa [sharpDiagram_vertices] using v.property :
      v.val = Finsupp.single 1 3 ∨ v.val = Finsupp.single 0 3) with h | h <;>
    simpa [h, sharpGenerators, Finsupp.ext_iff] using (isHomogeneous_X A _).pow 3

private theorem span_sharpDiagram_eq_of_lt (A : Type*) [CommSemiring A] {k : ℕ} (hk : k < 6) :
    Submodule.span A (sharpDiagram.diagramSpanSet (sharpGenerators A) k) =
      homogeneousSubmodule (Fin 2) A k := by
  refine le_antisymm
    (Set.span_diagramSpanSet_le_homogeneousSubmodule (isHomogeneous_sharpGenerators A) k)
    (homogeneousSubmodule_le_iff.mpr fun s hs ↦ Submodule.subset_span ?_)
  have hs_sum : s 0 + s 1 = k := by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hs
  -- Helper packaging a monomial `s` with `3 ≤ s i` via vertex `Finsupp.single j 3`.
  have hmem (i j : Fin 2) (hi : 3 ≤ s i) (hvj : Finsupp.single j 3 ∈ sharpDiagram.diagramVertices)
      (hbi : s - Finsupp.single i 3 ∈ sharpDiagram.diagramBox (Finsupp.single j 3))
      (hgen : sharpGenerators A ⟨Finsupp.single j 3, hvj⟩ = X i ^ 3) :
      monomial s (1 : A) ∈ sharpDiagram.diagramSpanSet (sharpGenerators A) k := by
    have h := congrArg Finsupp.degree (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi))
    simp only [map_add, Finsupp.degree_single, hs] at h
    simpa [hgen, X_pow_eq_monomial, monomial_mul_monomial, one_mul, tsub_add_cancel_of_le
      (Finsupp.single_le_iff.mpr hi)] using Set.monomial_mul_mem_diagramSpanSet
      (H := sharpGenerators A) (ℓ := k) ⟨Finsupp.single j 3, hvj⟩ hbi (by simp; omega)
  by_cases hs0 : 3 ≤ s 0
  · exact hmem 0 1 hs0 (by simp [sharpDiagram_vertices]) (Set.mem_diagramBox_iff.mpr
      fun α' hα' hlt _ ↦ (by simpa [sharpDiagram_vertices] using hα' : α' = Finsupp.single 1 3 ∨
        α' = Finsupp.single 0 3).elim (fun h ↦ hlt.ne (congrArg _ h)) fun h ↦
        (h ▸ toDegLex_sharpDiagram_lt).not_gt hlt) (by simp [sharpGenerators])
  · by_cases hs1 : 3 ≤ s 1
    · exact hmem 1 0 hs1 (by simp [sharpDiagram_vertices])
        ((mem_diagramBox_sharpDiagram_single_zero_three_iff _).mpr (by simp; omega))
        (by simp [sharpGenerators, Finsupp.ext_iff])
    · exact Set.monomial_mem_diagramSpanSet (by simp [sharpDiagram]; omega) hs

private theorem span_sharpDiagram_six_ne (A : Type*) [CommSemiring A] [Nontrivial A] :
    Submodule.span A (sharpDiagram.diagramSpanSet (sharpGenerators A) 6) ≠
      homogeneousSubmodule (Fin 2) A 6 := by
  -- Evaluate at `(0, 1)`: every generator of `sharpDiagram.diagramSpanSet` in degree `6` vanishes,
  -- whereas `X 1 ^ 6` evaluates to `1`.
  intro hspan6
  refine absurd ((Submodule.image_span_subset
      (aeval (R := A) ![0, (1 : A)]).toLinearMap _ ⊥).mpr (fun g hg ↦ ?_)
      ⟨X 1 ^ 6, hspan6 ▸ (mem_homogeneousSubmodule 6 _).mpr ((isHomogeneous_X A _).pow 6), rfl⟩)
    (by simp)
  simp only [Submodule.mem_bot, AlgHom.toLinearMap_apply]
  rcases hg with ⟨v, β, hβ, hdeg, rfl⟩ | ⟨γ, hγ, hdeg, rfl⟩
  · rw [map_mul]
    rcases (by simpa [sharpDiagram_vertices] using v.property :
        v.val = Finsupp.single 1 3 ∨ v.val = Finsupp.single 0 3) with h | h
    · simp [sharpGenerators, h]
    · have := (mem_diagramBox_sharpDiagram_single_zero_three_iff β).mp (h ▸ hβ)
      rw [h, Finsupp.degree_single, Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      simp [show β 0 ≠ 0 by omega, sharpGenerators, h, Finsupp.ext_iff]
  · rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
    exact absurd (by omega : 3 ≤ γ 1 ∨ 3 ≤ γ 0) hγ

/-- Sharpness of `Set.diagramCutoff`: over any nontrivial commutative semiring `A`, there exist an
upward-closed monotone diagram `D` on `Fin 2` with `0 < D.diagramCutoff` and homogeneous
polynomials `H` of degrees `v.val.degree` such that `D.diagramSpanSet H k` spans
`homogeneousSubmodule (Fin 2) A k` for every `k < D.diagramCutoff`, yet
`D.diagramSpanSet H D.diagramCutoff` fails to span
`homogeneousSubmodule (Fin 2) A D.diagramCutoff`.

In the proof, this is witnessed by the concrete example `{γ : Fin 2 →₀ ℕ | 3 ≤ γ 1 ∨ 3 ≤ γ 0}`
(which has vertices of degree `3` and cutoff `6`) and generators `X 0 ^ 3`, `X 1 ^ 3`. -/
theorem exists_isMonotoneDiagram_forall_lt_diagramCutoff_and_span_ne
    (A : Type*) [CommSemiring A] [Nontrivial A] :
    ∃ (D : Set (Fin 2 →₀ ℕ)) (H : D.diagramVertices → MvPolynomial (Fin 2) A),
      IsUpperSet D ∧ D.IsMonotoneDiagram ∧ (∀ v, (H v).IsHomogeneous v.val.degree) ∧
      0 < D.diagramCutoff ∧
      (∀ k < D.diagramCutoff,
        Submodule.span A (D.diagramSpanSet H k) = homogeneousSubmodule (Fin 2) A k) ∧
      Submodule.span A (D.diagramSpanSet H D.diagramCutoff) ≠
        homogeneousSubmodule (Fin 2) A D.diagramCutoff :=
  ⟨sharpDiagram, sharpGenerators A, isUpperSet_sharpDiagram, isMonotoneDiagram_sharpDiagram,
    isHomogeneous_sharpGenerators A, by rw [diagramCutoff_sharpDiagram]; omega,
    fun _ hk ↦ span_sharpDiagram_eq_of_lt A (diagramCutoff_sharpDiagram ▸ hk),
    diagramCutoff_sharpDiagram ▸ span_sharpDiagram_six_ne A⟩

end CutoffSharpness

end TauCeti
