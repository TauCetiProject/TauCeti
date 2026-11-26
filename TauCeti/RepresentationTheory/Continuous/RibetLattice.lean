/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo
import TauCeti.LinearAlgebra.Matrix.Charpoly.Henselian
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LineHyperplane
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Descend

/-!
# Ribet's lemma: lattices with nonsplit reduction

Let `A → K` be an injective map from a henselian local ring with residue field `k` to a normed
field, whose image contains the closed unit ball of `K` (for instance the ring of integers of a
finite extension `K` of `ℚ_p`), and let `ρ : G → GL₂(K)` be a continuous irreducible
representation of a compact group whose characteristic polynomials are integral and reduce to
`(X - χ g) (X - ψ g)` for two distinct characters `χ ψ : G → kˣ`. Ribet's lemma says that `ρ`
stabilizes a lattice whose reduction is a nonsplit extension of `ψ` by `χ`: in a suitable basis
the reduced matrices are `!![χ g, b g; 0, ψ g]` and `b` is not a coboundary, that is, not of the
form `(ψ - χ) v` for a constant `v ∈ k`.

This is the starting point of Ribet's method for constructing nontrivial extensions of
characters from congruences between Galois representations, and of the lattice/trace comparisons
for residually reducible deformations.

## Implementation notes

The proof follows Ribet. Since `χ ≠ ψ` some `ρ g₀` has residually distinct eigenvalues, which lift
to `A` by Hensel's lemma. In an eigenbasis of `ρ g₀` the traces of `ρ g` and `ρ (g₀ g)` show that
the diagonal entries of every `ρ g` are integral with residues `χ g` and `ψ g`, and the product of
the upper right entry of `ρ g` with the lower left entry of `ρ h` is integral with residue `0`.
By compactness the norm of the upper right entry `b g` is maximal at some `g₁`, and `b g₁ ≠ 0` by
irreducibility. Dividing the second basis vector by `b g₁` makes every entry integral, the lower
left entries residually zero and `b g₁ = 1`, while `b g₀ = 0` rules out a coboundary.

## Main results

* `TauCeti.exists_stable_lattice_nonsplit_reduction`: Ribet's lemma.

## References

* K. A. Ribet, *A modular construction of unramified p-extensions of ℚ(μ_p)*, Invent. Math. 34
  (1976), Proposition 2.1.
-/

public section

open Polynomial IsLocalRing Matrix

namespace TauCeti

variable {A K : Type*} [CommRing A] [IsLocalRing A] [NormedField K] [Algebra A K]

variable {G : Type*} [Group G]

/-- If `N g₀` is diagonal with integral, residually distinct entries, then the diagonal entries of
every `N g` are integral, with residues `χ g` and `ψ g`, provided all traces are integral with
residues `χ + ψ`. -/
private theorem exists_diagonal_entries (N : G →* (Matrix (Fin 2) (Fin 2) K)ˣ)
    (χ ψ : G →* (ResidueField A)ˣ)
    (htr : ∀ g, ∃ t : A, algebraMap A K t = (N g : Matrix (Fin 2) (Fin 2) K).trace ∧
      residue A t = χ g + ψ g)
    {g₀ : G} {α β : A}
    (hN₀ : (N g₀ : Matrix (Fin 2) (Fin 2) K) = diagonal ![algebraMap A K α, algebraMap A K β])
    (hα : residue A α = χ g₀) (hβ : residue A β = ψ g₀)
    (hg₀ : (χ g₀ : ResidueField A) ≠ ψ g₀) (g : G) :
    ∃ x y : A, algebraMap A K x = (N g : Matrix (Fin 2) (Fin 2) K) 0 0 ∧
      algebraMap A K y = (N g : Matrix (Fin 2) (Fin 2) K) 1 1 ∧
      residue A x = χ g ∧ residue A y = ψ g := by
  obtain ⟨t, ht, ht'⟩ := htr g
  obtain ⟨s, hs, hs'⟩ := htr (g₀ * g)
  obtain ⟨w, hw⟩ : IsUnit (α - β) :=
    (residue_ne_zero_iff_isUnit _).mp (by rwa [map_sub, hα, hβ, sub_ne_zero])
  rw [trace_fin_two] at ht
  rw [map_mul, Units.val_mul, hN₀, trace_fin_two] at hs
  simp only [diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
  simp only [map_mul, Units.val_mul] at hs'
  have hwK : algebraMap A K ↑w⁻¹ * (algebraMap A K α - algebraMap A K β) = 1 := by
    rw [← map_sub, ← hw, ← map_mul, Units.inv_mul, map_one]
  have hwk : residue A ↑w⁻¹ * (χ g₀ - ψ g₀) = 1 := by
    rw [← hα, ← hβ, ← map_sub, ← hw, ← map_mul, Units.inv_mul, map_one]
  have hx : algebraMap A K (↑w⁻¹ * (s - β * t)) = (N g : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    simp only [map_mul, map_sub]
    linear_combination algebraMap A K ↑w⁻¹ * hs - algebraMap A K ↑w⁻¹ * algebraMap A K β * ht +
      (N g : Matrix (Fin 2) (Fin 2) K) 0 0 * hwK
  have hxr : residue A (↑w⁻¹ * (s - β * t)) = χ g := by
    simp only [map_mul, map_sub, hβ]
    linear_combination residue A ↑w⁻¹ * hs' - residue A ↑w⁻¹ * (ψ g₀ : ResidueField A) * ht' +
      (χ g : ResidueField A) * hwk
  refine ⟨_, t - ↑w⁻¹ * (s - β * t), hx, ?_, hxr, ?_⟩
  · rw [map_sub, hx, ht]; ring
  · rw [map_sub, hxr, ht']; ring

variable [FaithfulSMul A K]

/-- The rescaling step of Ribet's lemma. Suppose the diagonal entries of the matrices `N g` are
integral with residues `χ g` and `ψ g`, that `N g₀` is upper right zero with `χ g₀ ≠ ψ g₀`, and that
the upper right entry of `N g₁` is nonzero of maximal norm. Rescaling the second basis vector by
that entry conjugates `N` into `GL₂(A)` with nonsplit reduction. -/
private theorem exists_conj_lift_nonsplit
    (hA : ∀ x : K, ‖x‖ ≤ 1 → ∃ a : A, algebraMap A K a = x)
    (N : G →* (Matrix (Fin 2) (Fin 2) K)ˣ) (χ ψ : G →* (ResidueField A)ˣ) {x y : G → A}
    (hx : ∀ g, algebraMap A K (x g) = (N g : Matrix (Fin 2) (Fin 2) K) 0 0)
    (hy : ∀ g, algebraMap A K (y g) = (N g : Matrix (Fin 2) (Fin 2) K) 1 1)
    (hxr : ∀ g, residue A (x g) = χ g) (hyr : ∀ g, residue A (y g) = ψ g)
    {g₀ g₁ : G} (hg₀ : (χ g₀ : ResidueField A) ≠ ψ g₀)
    (h01 : (N g₀ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hb₁ : (N g₁ : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0)
    (hg₁ : ∀ g, ‖(N g : Matrix (Fin 2) (Fin 2) K) 0 1‖ ≤ ‖(N g₁ : Matrix (Fin 2) (Fin 2) K) 0 1‖) :
    ∃ (D : (Matrix (Fin 2) (Fin 2) K)ˣ) (ρA : G →* (Matrix (Fin 2) (Fin 2) A)ˣ),
      (∀ g i j, algebraMap A K ((ρA g : Matrix (Fin 2) (Fin 2) A) i j) =
        ((↑D⁻¹ : Matrix (Fin 2) (Fin 2) K) * N g * D) i j) ∧
      (∀ g, residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 0 0) = χ g ∧
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 1 1) = ψ g ∧
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 1 0) = 0) ∧
      ¬ ∃ v : ResidueField A, ∀ g,
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 0 1) =
          ((ψ g : ResidueField A) - (χ g : ResidueField A)) * v := by
  have hinj := FaithfulSMul.algebraMap_injective A K
  set b₁ := (N g₁ : Matrix (Fin 2) (Fin 2) K) 0 1
  -- Products of opposite off-diagonal entries are integral with residue zero.
  have hbc (g h : G) : (N g : Matrix (Fin 2) (Fin 2) K) 0 1 * (N h : Matrix (Fin 2) (Fin 2) K) 1 0 =
      algebraMap A K (x (g * h) - x g * x h) := by
    rw [map_sub, map_mul, hx, hx, hx, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hbcr (g h : G) : residue A (x (g * h) - x g * x h) = 0 := by
    rw [map_sub, map_mul, hxr, hxr, hxr, map_mul, Units.val_mul, sub_self]
  let D : (Matrix (Fin 2) (Fin 2) K)ˣ := ⟨diagonal ![1, b₁⁻¹], diagonal ![1, b₁],
    by simp [funext_iff, Fin.forall_fin_two, hb₁], by simp [funext_iff, Fin.forall_fin_two, hb₁]⟩
  set N' := (MulAut.conj D⁻¹).toMonoidHom.comp N
  have hN' (g : G) : (N' g : Matrix (Fin 2) (Fin 2) K) =
      diagonal ![1, b₁] * N g * diagonal ![1, b₁⁻¹] := by simp [N', D]
  have hint (g : G) (i j : Fin 2) :
      ∃ z : A, algebraMap A K z = (N' g : Matrix (Fin 2) (Fin 2) K) i j := by
    rw [hN', diagonal_vec2_one_mul_mul_diagonal_vec2_one_inv hb₁]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, of_apply, cons_val_zero, cons_val_one]
    · exact ⟨x g, hx g⟩
    · refine hA _ ?_
      rw [norm_mul, norm_inv]
      exact mul_inv_le_one_of_le₀ (hg₁ g) (norm_nonneg _)
    · exact ⟨x (g₁ * g) - x g₁ * x g, (hbc g₁ g).symm⟩
    · exact ⟨y g, hy g⟩
  have hent : CoefficientDescent.entries N' ⊆ Set.range (algebraMap A K) := by
    intro _ hz
    obtain ⟨g, i, j, rfl⟩ := CoefficientDescent.mem_entries_iff.mp hz
    exact hint g i j
  set ρA := CoefficientDescent.descend hinj hent
  have hρA := CoefficientDescent.map_descend_apply hinj hent
  have hρA' (g : G) (i j : Fin 2) : algebraMap A K ((ρA g : Matrix (Fin 2) (Fin 2) A) i j) =
      !![(N g : Matrix (Fin 2) (Fin 2) K) 0 0, (N g : Matrix (Fin 2) (Fin 2) K) 0 1 * b₁⁻¹;
        b₁ * (N g : Matrix (Fin 2) (Fin 2) K) 1 0, (N g : Matrix (Fin 2) (Fin 2) K) 1 1] i j := by
    rw [hρA, hN', diagonal_vec2_one_mul_mul_diagonal_vec2_one_inv hb₁]
  refine ⟨D, ρA, hρA, fun g => ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hinj ((hρA' g 0 0).trans (hx g).symm), hxr]
  · rw [hinj ((hρA' g 1 1).trans (hy g).symm), hyr]
  · rw [hinj ((hρA' g 1 0).trans (hbc g₁ g)), hbcr]
  · rintro ⟨v, hv⟩
    have h0 : (ρA g₀ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 :=
      hinj (by rw [hρA']; simp [h01])
    have h1 : (ρA g₁ : Matrix (Fin 2) (Fin 2) A) 0 1 = 1 :=
      hinj (by rw [hρA']; simp [b₁, hb₁])
    have hv0 : v = 0 := by
      have := hv g₀
      rw [h0, map_zero, eq_comm, mul_eq_zero, sub_eq_zero] at this
      exact this.resolve_left hg₀.symm
    simpa [h1, hv0] using hv g₁

/-- The matrix form of Ribet's lemma: `ρ` is conjugate in `GL₂(K)` to a homomorphism to
`GL₂(A)` whose reduction is a nonsplit extension of `ψ` by `χ`. -/
private theorem exists_conj_nonsplit [HenselianRing A (maximalIdeal A)]
    (hA : ∀ x : K, ‖x‖ ≤ 1 → ∃ a : A, algebraMap A K a = x)
    [TopologicalSpace G] [CompactSpace G]
    (ρ : G →* (Matrix (Fin 2) (Fin 2) K)ˣ)
    (hρ : Continuous fun g ↦ (ρ g : Matrix (Fin 2) (Fin 2) K))
    (hirr : ∀ W : Submodule K (Fin 2 → K),
      (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin 2) (Fin 2) K) *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (χ ψ : G →* (ResidueField A)ˣ) (hdistinct : χ ≠ ψ)
    (hchar : ∀ g, ∃ P : A[X],
      P.map (algebraMap A K) = (ρ g : Matrix (Fin 2) (Fin 2) K).charpoly ∧
      P.map (residue A) = (X - C (χ g : ResidueField A)) * (X - C (ψ g : ResidueField A))) :
    ∃ (Q : (Matrix (Fin 2) (Fin 2) K)ˣ) (ρA : G →* (Matrix (Fin 2) (Fin 2) A)ˣ),
      (∀ g i j, algebraMap A K ((ρA g : Matrix (Fin 2) (Fin 2) A) i j) =
        ((↑Q⁻¹ : Matrix (Fin 2) (Fin 2) K) * ρ g * Q) i j) ∧
      (∀ g, residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 0 0) = χ g ∧
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 1 1) = ψ g ∧
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 1 0) = 0) ∧
      ¬ ∃ v : ResidueField A, ∀ g,
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 0 1) =
          ((ψ g : ResidueField A) - (χ g : ResidueField A)) * v := by
  choose P hP hPr using hchar
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, (χ g₀ : ResidueField A) ≠ ψ g₀ := by
    by_contra! h
    exact hdistinct (MonoidHom.ext fun g => Units.ext (h g))
  -- Diagonalize `ρ g₀`, whose eigenvalues are integral and residually distinct.
  obtain ⟨Q₀, α, β, hQ₀, hα, hβ⟩ :=
    exists_conj_eq_diagonal_of_henselian_fin_two hg₀ (hP g₀) (hPr g₀)
  set N₀ : G →* (Matrix (Fin 2) (Fin 2) K)ˣ := (MulAut.conj Q₀⁻¹).toMonoidHom.comp ρ
  have hN₀ (g : G) : (N₀ g : Matrix (Fin 2) (Fin 2) K) =
      (↑Q₀⁻¹ : Matrix (Fin 2) (Fin 2) K) * ρ g * Q₀ := by
    simp [N₀]
  have htr (g : G) : ∃ t : A, algebraMap A K t = (N₀ g : Matrix (Fin 2) (Fin 2) K).trace ∧
      residue A t = χ g + ψ g := by
    rw [hN₀, trace_mul_cycle, Units.mul_inv, Matrix.one_mul]
    exact exists_algebraMap_eq_trace_fin_two (hP g) (hPr g)
  choose x y hx hy hxr hyr using
    exists_diagonal_entries N₀ χ ψ htr (hN₀ g₀ ▸ hQ₀) hα hβ hg₀
  -- Choose `g₁` maximizing the norm of the upper right entry; it is nonzero by irreducibility.
  obtain ⟨g', hg'⟩ : ∃ g, (N₀ g : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := by
    obtain ⟨g, hg⟩ := exists_conj_notMem_lineStabilizer ρ hirr Q₀ 1
    refine ⟨g, fun h0 => hg (mem_lineStabilizer_iff.mpr fun j hj => ?_)⟩
    fin_cases j
    · simpa [hN₀] using h0
    · exact absurd rfl hj
  have hcont : Continuous fun g => ‖(N₀ g : Matrix (Fin 2) (Fin 2) K) 0 1‖ := by
    simp only [hN₀]
    exact ((continuous_const.matrix_mul hρ).matrix_mul continuous_const).matrix_elem 0 1 |>.norm
  obtain ⟨g₁, -, hg₁⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hb₁ : (N₀ g₁ : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := norm_pos_iff.mp <|
    (norm_pos_iff.mpr hg').trans_le (hg₁ (Set.mem_univ g'))
  obtain ⟨D, ρA, hρA, hres, hns⟩ := exists_conj_lift_nonsplit hA N₀ χ ψ hx hy hxr hyr hg₀
    (by rw [hN₀, hQ₀]; simp) hb₁ fun g => hg₁ (Set.mem_univ g)
  refine ⟨Q₀ * D, ρA, fun g i j => ?_, hres, hns⟩
  rw [hρA, hN₀, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

/-- **Ribet's lemma.** Let `A → K` be an injective map from a henselian local ring to a normed
field whose image contains the closed unit ball, and let `ρ : G → GL₂(K)` be a continuous
irreducible representation of a compact group whose characteristic polynomials are integral, with
reductions `(X - χ g) (X - ψ g)` for distinct characters `χ ψ : G → kˣ` of the residue field `k`.
Then `ρ` preserves a lattice `L ⊆ K²` with a basis in which `ρ` is given by matrices `ρA g` over
`A` whose reductions are upper triangular with diagonal `(χ, ψ)`, and the upper right entry is not
a coboundary: the reduction of `L` is a nonsplit extension of `ψ` by `χ`. -/
theorem exists_stable_lattice_nonsplit_reduction [HenselianRing A (maximalIdeal A)]
    (hA : ∀ x : K, ‖x‖ ≤ 1 → ∃ a : A, algebraMap A K a = x)
    [TopologicalSpace G] [CompactSpace G]
    (ρ : G →* (Matrix (Fin 2) (Fin 2) K)ˣ)
    (hρ : Continuous fun g ↦ (ρ g : Matrix (Fin 2) (Fin 2) K))
    (hirr : ∀ W : Submodule K (Fin 2 → K),
      (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin 2) (Fin 2) K) *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (χ ψ : G →* (ResidueField A)ˣ) (hdistinct : χ ≠ ψ)
    (hchar : ∀ g, ∃ P : A[X],
      P.map (algebraMap A K) = (ρ g : Matrix (Fin 2) (Fin 2) K).charpoly ∧
      P.map (residue A) = (X - C (χ g : ResidueField A)) * (X - C (ψ g : ResidueField A))) :
    ∃ (L : Submodule A (Fin 2 → K)) (b : Module.Basis (Fin 2) A L)
      (ρA : G →* (Matrix (Fin 2) (Fin 2) A)ˣ),
      Submodule.span K (L : Set (Fin 2 → K)) = ⊤ ∧
      (∀ g i, (ρ g : Matrix (Fin 2) (Fin 2) K) *ᵥ (b i : Fin 2 → K) =
        ∑ j, (ρA g : Matrix (Fin 2) (Fin 2) A) j i • (b j : Fin 2 → K)) ∧
      (∀ g, residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 0 0) = χ g ∧
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 1 1) = ψ g ∧
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 1 0) = 0) ∧
      ¬ ∃ v : ResidueField A, ∀ g,
        residue A ((ρA g : Matrix (Fin 2) (Fin 2) A) 0 1) =
          ((ψ g : ResidueField A) - (χ g : ResidueField A)) * v := by
  obtain ⟨Q, ρA, hQ, hres, hns⟩ := exists_conj_nonsplit hA ρ hρ hirr χ ψ hdistinct hchar
  have hli : LinearIndependent K (Q : Matrix (Fin 2) (Fin 2) K).col :=
    linearIndependent_col_iff_isUnit.mpr Q.isUnit
  refine ⟨_, .span (hli.restrict_scalars' A), ρA, ?_, fun g i => ?_, hres, hns⟩
  · rw [Submodule.span_span_of_tower]
    exact hli.span_eq_top_of_card_eq_finrank' (by simp)
  · simp only [Module.Basis.span_apply]
    have hρQ : (ρ g : Matrix (Fin 2) (Fin 2) K) * Q =
        Q * ((↑Q⁻¹ : Matrix (Fin 2) (Fin 2) K) * ρ g * Q) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    ext k
    have := congrFun (congrFun hρQ k) i
    simp only [Matrix.mul_apply, Fin.sum_univ_two, ← hQ] at this
    simp only [mulVec, dotProduct, Fin.sum_univ_two, col_apply, Pi.add_apply, Pi.smul_apply,
      this]
    simp only [Algebra.smul_def]
    ring

end TauCeti
