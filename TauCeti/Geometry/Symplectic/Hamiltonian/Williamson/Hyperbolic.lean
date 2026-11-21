/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Nondegenerate
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral
import Mathlib.Data.Finset.Sort
import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair

/-!
# Williamson's classification of nondegenerate families: the hyperbolic case

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic forms
on `V` is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the
Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`. Williamson's
classification puts such a family, up to its span, into a normal form made of elliptic,
hyperbolic and focus-focus blocks in a suitable Darboux basis. This file proves the classification
for the **split** Cartan subalgebras, those containing an element with `dim V` distinct real
eigenvalues:

`∃ P ∈ span Q, A_P has dim V distinct real eigenvalues  ↔  span Q = span (H₁, …, Hₙ)`

for the hyperbolic blocks `Hₖ = xₖ yₖ` (`TauCeti.SymplecticForm.hyperbolic`) of some Darboux basis
`(q₁, p₁, …, qₙ, pₙ)`
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.exists_mem_span_card_eq_finrank_iff`).
In particular every form in the span of such a family is a combination `∑ₖ cₖ xₖ yₖ` in these
common coordinates.

The proof has two steps.

* **Normal form of a regular hyperbolic Hamiltonian.** Let `A_P` have `dim V` distinct real
  eigenvalues, with eigenvectors `e_μ`; they form a basis. Since `A_P ∈ sp(V, ω)`,
  `(μ + ν) ω(e_μ, e_ν) = 0`, so by nondegeneracy each `e_μ` pairs nontrivially with some `e_ν`
  and then `ν = -μ`. Hence the eigenvalues are `±a₁, …, ±aₙ` with `aₖ > 0`, and the eigenvectors
  `qₖ = e_(aₖ)` together with suitably rescaled `pₖ ∝ e_(-aₖ)` form a Darboux basis in which
  `P = ∑ₖ aₖ xₖ yₖ`
  (`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_hyperbolic`).
* **Equality of spans.** The forms `Q i` Poisson-commute with `P`, since `𝔥` is abelian, and the
  coefficients `aₖ` are nonzero with distinct squares, so every `Q i` is a combination of the
  hyperbolic blocks
  (`IsDarbouxBasis.mem_span_hyperbolic_of_quadraticPoissonBracket_eq_zero` in the namespace
  `TauCeti.SymplecticForm`).
  The hyperbolic blocks Poisson-commute, and a nondegenerate family is maximal among
  Poisson-commuting families
  (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.span_eq_of_span_le`), so the two spans
  are equal.

Conversely the form `∑ₖ (k + 1) xₖ yₖ` has the `2n` distinct eigenvalues `±(k + 1)`.

## Main results

All declarations are in the namespace `TauCeti.SymplecticForm`.

* `exists_isDarbouxBasis_eq_sum_smul_hyperbolic`: a quadratic form whose Hamiltonian endomorphism
  has `dim V` distinct real eigenvalues is `∑ₖ aₖ xₖ yₖ` with `0 < a₁ < ⋯ < aₙ` in some Darboux
  basis.
* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_hyperbolic`: a nondegenerate
  family whose span contains such a form spans the hyperbolic blocks of a Darboux basis.
* `IsNondegenerateQuadraticFamily.exists_mem_span_card_eq_finrank_iff`: this characterizes the
  nondegenerate families of purely hyperbolic type.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

open Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}

/-- The values `±cₖ` of an injective positive family `c` are pairwise distinct. -/
private theorem injective_matrixVecCons_neg {n : ℕ} {c : Fin n → ℝ} (hc : Function.Injective c)
    (hpos : ∀ k, 0 < c k) : Function.Injective fun i : Fin n × Fin 2 ↦ ![c i.1, -c i.1] i.2 := by
  rintro ⟨k, i⟩ ⟨l, j⟩ h
  have hk := hpos k
  have hl := hpos l
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  all_goals obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  all_goals
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_inj] at h
  · rw [hc h]
  · linarith
  · linarith
  · rw [hc h]

/-- If the Hamiltonian endomorphism `A_P` has `dim V` distinct real eigenvalues `μ ∈ s`, with
eigenvectors `e μ`, then each `e μ` pairs nontrivially with the eigenvector `e ν` for `ν = -μ`; in
particular `-μ ∈ s`. -/
private theorem exists_neg_apply_ne_zero {P : QuadraticForm ℝ V} {s : Finset ℝ}
    (hs : s.card = finrank ℝ V) {e : s → V}
    (he : ∀ μ : s, (ω.hamiltonianEnd P).HasEigenvector μ (e μ)) (μ : s) :
    ∃ ν : s, (ν : ℝ) = -μ ∧ ω (e μ) (e ν) ≠ 0 := by
  have hA := (LinearMap.mem_skewAdjointSubmodule _).1
    (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P)
  -- The eigenvectors form a basis, and `ω (e μ)` vanishes on every `e ν` with `ν ≠ -μ`.
  have hli := (ω.hamiltonianEnd P).eigenvectors_linearIndependent' (fun μ : s ↦ (μ : ℝ))
    Subtype.coe_injective e he
  let E := basisOfLinearIndependentOfCardEqFinrank' e hli (by simpa using hs)
  by_contra! hcon
  have h0 : ω.toBilinForm (e μ) = 0 := E.ext fun ν ↦ by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank', LinearMap.zero_apply]
    by_cases hν : (ν : ℝ) = -μ
    · exact hcon ν hν
    · exact hA.apply_eq_zero_of_mem_genEigenspace (isUnit_iff_ne_zero.2 fun h ↦ hν (by linarith))
        (he μ).1 (he ν).1
  exact (he μ).2 (ω.nondegenerate.1 _ fun w ↦ by rw [h0, LinearMap.zero_apply])

/-- A basis `(q₁, p₁, …, qₙ, pₙ)` of eigenvectors of `A_P`, with `A_P qₖ = aₖ qₖ` and
`A_P pₖ = -aₖ pₖ` for distinct positive `aₖ` and with `ω(qₖ, pₖ) = 1`, is a Darboux basis: `ω`
pairs eigenvectors trivially unless their eigenvalues add up to `0`. -/
private theorem isDarbouxBasis_of_hasEigenvector {P : QuadraticForm ℝ V} {n : ℕ}
    {b : Basis (Fin n × Fin 2) ℝ V} {a : Fin n → ℝ} (ha : Function.Injective a)
    (ha0 : ∀ k, 0 < a k) (hq : ∀ k, (ω.hamiltonianEnd P).HasEigenvector (a k) (b (k, 0)))
    (hp : ∀ k, (ω.hamiltonianEnd P).HasEigenvector (-a k) (b (k, 1)))
    (hqp : ∀ k, ω (b (k, 0)) (b (k, 1)) = 1) : ω.IsDarbouxBasis b := by
  have hA := (LinearMap.mem_skewAdjointSubmodule _).1
    (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P)
  have horth {μ ν : ℝ} {u v : V} (hu : (ω.hamiltonianEnd P).HasEigenvector μ u)
      (hv : (ω.hamiltonianEnd P).HasEigenvector ν v) (hμν : μ + ν ≠ 0) : ω u v = 0 :=
    hA.apply_eq_zero_of_mem_genEigenspace hμν.isUnit hu.1 hv.1
  refine ⟨fun k l ↦ horth (hq k) (hq l) (add_pos (ha0 k) (ha0 l)).ne',
    fun k l ↦ horth (hp k) (hp l) (add_neg (neg_neg_of_pos (ha0 k)) (neg_neg_of_pos (ha0 l))).ne,
    fun k l ↦ ?_⟩
  split_ifs with hkl
  · exact hkl ▸ hqp k
  · exact horth (hq k) (hp l) fun h ↦ hkl (ha (by linarith))

/-- A finite set `s` of reals, stable under negation and not containing `0`, is enumerated by the
values `±aₖ`, where `a₀ < ⋯ < aₙ₋₁` are its positive elements. -/
private theorem image_univ_matrixVecCons_neg_orderEmbOfFin {s : Finset ℝ}
    (hneg : ∀ μ ∈ s, -μ ∈ s) (hzero : (0 : ℝ) ∉ s) :
    Finset.univ.image (fun i : Fin (s.filter (0 < ·)).card × Fin 2 ↦
      ![(s.filter (0 < ·)).orderEmbOfFin rfl i.1, -(s.filter (0 < ·)).orderEmbOfFin rfl i.1] i.2) =
      s := by
  set t := s.filter (0 < ·)
  have hrange : Set.range (t.orderEmbOfFin rfl) = t := Finset.range_orderEmbOfFin t rfl
  ext μ
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨k, i⟩, rfl⟩
    have hk := (Finset.mem_filter.1 (t.orderEmbOfFin_mem rfl k)).1
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · simpa using hk
    · simpa using hneg _ hk
  · intro hμ
    rcases lt_or_gt_of_ne (show μ ≠ 0 from fun h ↦ hzero (h ▸ hμ)) with hμ0 | hμ0
    · obtain ⟨k, hk⟩ : -μ ∈ Set.range (t.orderEmbOfFin rfl) := by
        rw [hrange, Finset.mem_coe, Finset.mem_filter]
        exact ⟨hneg μ hμ, by linarith⟩
      exact ⟨(k, 1), by simp [hk]⟩
    · obtain ⟨k, hk⟩ : μ ∈ Set.range (t.orderEmbOfFin rfl) := by
        rw [hrange, Finset.mem_coe, Finset.mem_filter]
        exact ⟨hμ, hμ0⟩
      exact ⟨(k, 0), by simp [hk]⟩

variable (ω) in
/-- **A Darboux basis of eigenvectors of a regular hyperbolic Hamiltonian.** If the Hamiltonian
endomorphism `A_P` of a quadratic form `P` has `dim V` distinct real eigenvalues, listed in a
finite set `s`, then there are a Darboux basis `(q₁, p₁, …, qₙ, pₙ)` and reals
`0 < a₁ < ⋯ < aₙ` with `A_P qₖ = aₖ qₖ` and `A_P pₖ = -aₖ pₖ`. -/
theorem exists_isDarbouxBasis_hamiltonianEnd_apply_eq {P : QuadraticForm ℝ V} {s : Finset ℝ}
    (hs : s.card = finrank ℝ V) (hP : ∀ μ ∈ s, (ω.hamiltonianEnd P).HasEigenvalue μ) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (a : Fin n → ℝ), ω.IsDarbouxBasis b ∧
      StrictMono a ∧ (∀ k, 0 < a k) ∧ ∀ k, ω.hamiltonianEnd P (b (k, 0)) = a k • b (k, 0) ∧
        ω.hamiltonianEnd P (b (k, 1)) = -a k • b (k, 1) := by
  set A := ω.hamiltonianEnd P
  -- One eigenvector `e μ` for each `μ ∈ s`, paired nontrivially with `e (σ μ)`, `σ μ = -μ`.
  choose e he using fun μ : s ↦ (hP μ μ.property).exists_hasEigenvector
  choose σ hσ hσω using exists_neg_apply_ne_zero hs he
  have hneg (μ : ℝ) (hμ : μ ∈ s) : -μ ∈ s := hσ ⟨μ, hμ⟩ ▸ (σ ⟨μ, hμ⟩).property
  have hzero : (0 : ℝ) ∉ s := fun h0 ↦ by
    have hσ0 : σ ⟨0, h0⟩ = ⟨0, h0⟩ := Subtype.ext (by simp [hσ])
    exact hσω ⟨0, h0⟩ (by rw [hσ0, ω.self_eq_zero])
  -- The positive eigenvalues `0 < a₀ < ⋯ < aₙ₋₁`; the eigenvalues are the `±aₖ`.
  set t := s.filter (0 < ·)
  set n := t.card
  let a : Fin n → ℝ := fun k ↦ t.orderEmbOfFin rfl k
  have ha : StrictMono a := (t.orderEmbOfFin rfl).strictMono
  have hat (k : Fin n) : a k ∈ s ∧ 0 < a k := Finset.mem_filter.1 (t.orderEmbOfFin_mem rfl k)
  -- The Darboux basis `qₖ = e aₖ`, `pₖ = ω(qₖ, e (-aₖ))⁻¹ • e (-aₖ)`.
  let μ (k : Fin n) : s := ⟨a k, (hat k).1⟩
  let c (k : Fin n) : ℝ := (ω (e (μ k)) (e (σ (μ k))))⁻¹
  let f : Fin n × Fin 2 → V := fun i ↦ ![e (μ i.1), c i.1 • e (σ (μ i.1))] i.2
  let ev : Fin n × Fin 2 → ℝ := fun i ↦ ![a i.1, -a i.1] i.2
  have hf (k : Fin n) (i : Fin 2) : A.HasEigenvector (ev (k, i)) (f (k, i)) := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact he (μ k)
    · refine ⟨Module.End.mem_eigenspace_iff.2 ?_, smul_ne_zero (inv_ne_zero (hσω _)) (he _).2⟩
      simp [f, ev, μ, (he _).apply_eq_smul, hσ, smul_comm (c k)]
  have hev : Function.Injective ev := injective_matrixVecCons_neg ha.injective fun k ↦ (hat k).2
  have hcard : Fintype.card (Fin n × Fin 2) = finrank ℝ V := by
    rw [← hs, ← image_univ_matrixVecCons_neg_orderEmbOfFin hneg hzero,
      Finset.card_image_of_injective _ hev, Finset.card_univ]
  let b := basisOfLinearIndependentOfCardEqFinrank' f
    (A.eigenvectors_linearIndependent' ev hev f fun ⟨k, i⟩ ↦ hf k i) hcard
  have hbf' : ⇑b = f := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hbf (k : Fin n) (i : Fin 2) : A.HasEigenvector (ev (k, i)) (b (k, i)) := by
    rw [hbf']
    exact hf k i
  have hb : ω.IsDarbouxBasis b :=
    isDarbouxBasis_of_hasEigenvector ha.injective (fun k ↦ (hat k).2) (fun k ↦ hbf k 0)
      (fun k ↦ hbf k 1) fun k ↦ by
        simp only [hbf', f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          map_smul, smul_eq_mul, c]
        exact inv_mul_cancel₀ (hσω _)
  exact ⟨n, b, a, hb, ha, fun k ↦ (hat k).2, fun k ↦
    ⟨(hbf k 0).apply_eq_smul, (hbf k 1).apply_eq_smul⟩⟩

variable (ω) in
/-- **Williamson's normal form of a regular hyperbolic quadratic Hamiltonian.** If the Hamiltonian
endomorphism `A_P` of a quadratic form `P` has `dim V` distinct real eigenvalues, listed in a
finite set `s`, then there are a Darboux basis `(q₁, p₁, …, qₙ, pₙ)` and reals
`0 < a₁ < ⋯ < aₙ` with `P = ∑ₖ aₖ xₖ yₖ`. -/
theorem exists_isDarbouxBasis_eq_sum_smul_hyperbolic {P : QuadraticForm ℝ V} {s : Finset ℝ}
    (hs : s.card = finrank ℝ V) (hP : ∀ μ ∈ s, (ω.hamiltonianEnd P).HasEigenvalue μ) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (a : Fin n → ℝ), ω.IsDarbouxBasis b ∧
      StrictMono a ∧ (∀ k, 0 < a k) ∧ P = ∑ k, a k • hyperbolic b k := by
  obtain ⟨n, b, a, hb, ha, ha0, hA⟩ := ω.exists_isDarbouxBasis_hamiltonianEnd_apply_eq hs hP
  refine ⟨n, b, a, hb, ha, ha0, ω.hamiltonianEnd_injective (b.ext ?_)⟩
  rintro ⟨k, i⟩
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_fst, (hA k).1]
  · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_snd, (hA k).2]

namespace IsNondegenerateQuadraticFamily

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Williamson's classification, hyperbolic case.** If the span of a nondegenerate family `Q` of
quadratic forms contains a form whose Hamiltonian endomorphism has `dim V` distinct real
eigenvalues, then there is a Darboux basis whose hyperbolic blocks `Hₖ = xₖ yₖ` span the same
space as `Q`. -/
theorem exists_isDarbouxBasis_span_eq_span_hyperbolic (h : ω.IsNondegenerateQuadraticFamily Q)
    {P : QuadraticForm ℝ V} (hP : P ∈ Submodule.span ℝ (Set.range Q)) {s : Finset ℝ}
    (hs : s.card = finrank ℝ V) (hPs : ∀ μ ∈ s, (ω.hamiltonianEnd P).HasEigenvalue μ) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (hyperbolic b)) := by
  obtain ⟨n, b, a, hb, ha, ha0, rfl⟩ := ω.exists_isDarbouxBasis_eq_sum_smul_hyperbolic hs hPs
  refine ⟨n, b, hb, h.span_eq_of_span_le hb.quadraticPoissonBracket_hyperbolic
    (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨i, rfl⟩
  -- `Q i` Poisson-commutes with the regular element `∑ₖ aₖ Hₖ`, so it is a combination of the
  -- `Hₖ`.
  exact hb.mem_span_hyperbolic_of_quadraticPoissonBracket_eq_zero
    (fun k l hkl hsq ↦
      hkl (ha.injective ((pow_left_inj₀ (ha0 k).le (ha0 l).le two_ne_zero).1 hsq)))
    (fun k ↦ (ha0 k).ne')
    (ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero
      (Submodule.subset_span ⟨i, rfl⟩) hP)

/-- **Nondegenerate families of hyperbolic type.** The span of a nondegenerate family `Q` of
quadratic forms contains a form whose Hamiltonian endomorphism has `dim V` distinct real
eigenvalues exactly when it is the span of the hyperbolic blocks `Hₖ = xₖ yₖ` of some Darboux
basis. -/
theorem exists_mem_span_card_eq_finrank_iff (h : ω.IsNondegenerateQuadraticFamily Q) :
    (∃ P ∈ Submodule.span ℝ (Set.range Q), ∃ s : Finset ℝ, s.card = finrank ℝ V ∧
        ∀ μ ∈ s, (ω.hamiltonianEnd P).HasEigenvalue μ) ↔
      ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (hyperbolic b)) := by
  refine ⟨fun ⟨P, hP, s, hs, hPs⟩ ↦ h.exists_isDarbouxBasis_span_eq_span_hyperbolic hP hs hPs,
    fun ⟨n, b, hb, hspan⟩ ↦ ?_⟩
  -- The form `∑ₖ (k + 1) Hₖ` has the eigenvalues `±(k + 1)`, with eigenvectors `qₖ` and `pₖ`.
  let c : Fin n → ℝ := fun k ↦ k + 1
  let ev : Fin n × Fin 2 → ℝ := fun i ↦ ![c i.1, -c i.1] i.2
  have hc (k : Fin n) : 0 < c k := by positivity
  have hev : Function.Injective ev :=
    injective_matrixVecCons_neg (fun k l h ↦ Fin.ext (by simpa [c] using h)) hc
  refine ⟨∑ k, c k • hyperbolic b k, ?_, Finset.univ.image ev, ?_, ?_⟩
  · rw [hspan]
    exact Submodule.sum_mem _ fun k _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Finset.card_image_of_injective _ hev, Finset.card_univ, ← finrank_eq_card_basis b]
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ ⟨k, i⟩ rfl
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := b (k, i))
      ⟨Module.End.mem_eigenspace_iff.2 ?_, b.ne_zero _⟩
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_fst]
      simp [ev]
    · rw [hb.hamiltonianEnd_sum_smul_hyperbolic_apply_snd]
      simp [ev]

end IsNondegenerateQuadraticFamily

end TauCeti.SymplecticForm
