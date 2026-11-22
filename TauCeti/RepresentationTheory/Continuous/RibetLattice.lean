/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Henselian
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact

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

/-- The trace of a `2 × 2` matrix whose characteristic polynomial comes from `P` over `A` is
integral, and its residue is the sum of the residual roots of `P`. -/
private theorem exists_algebraMap_eq_trace {M : Matrix (Fin 2) (Fin 2) K} {P : A[X]}
    {u v : ResidueField A} (hP : P.map (algebraMap A K) = M.charpoly)
    (hPr : P.map (residue A) = (X - C u) * (X - C v)) :
    ∃ t : A, algebraMap A K t = M.trace ∧ residue A t = u + v := by
  rw [show (X - C u) * (X - C v) = X ^ 2 - C (u + v) * X + C (u * v) by
    simp only [C_add, C_mul]; ring] at hPr
  refine ⟨-P.coeff 1, ?_, ?_⟩
  · have h := congrArg (fun p => p.coeff 1) hP
    simp only [coeff_map, charpoly_fin_two] at h
    rw [map_neg, h]
    simp [coeff_C]
  · have h := congrArg (fun p => p.coeff 1) hPr
    simp only [coeff_map] at h
    rw [map_neg, h]
    simp [coeff_C]

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

/-- If `ρ` has no stable line, then in any basis some matrix `ρ g` has a nonzero upper
right entry. -/
private theorem exists_conj_apply_zero_one_ne_zero (ρ : G →* (Matrix (Fin 2) (Fin 2) K)ˣ)
    (hirr : ∀ W : Submodule K (Fin 2 → K),
      (∀ g, ∀ x ∈ W, (ρ g : Matrix (Fin 2) (Fin 2) K) *ᵥ x ∈ W) → W = ⊥ ∨ W = ⊤)
    (Q : (Matrix (Fin 2) (Fin 2) K)ˣ) :
    ∃ g, ((↑Q⁻¹ : Matrix (Fin 2) (Fin 2) K) * ρ g * Q) 0 1 ≠ 0 := by
  by_contra! h
  have hQQ (x : Fin 2 → K) :
      (↑Q⁻¹ : Matrix (Fin 2) (Fin 2) K) *ᵥ ((Q : Matrix (Fin 2) (Fin 2) K) *ᵥ x) = x := by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  set w := (Q : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 1 1 with hw_def
  have hw (g : G) : (ρ g : Matrix (Fin 2) (Fin 2) K) *ᵥ w =
      ((↑Q⁻¹ : Matrix (Fin 2) (Fin 2) K) * ρ g * Q) 1 1 • w := by
    set N : Matrix (Fin 2) (Fin 2) K := (↑Q⁻¹ : Matrix (Fin 2) (Fin 2) K) * ρ g * Q with hN_def
    have hN : (ρ g : Matrix (Fin 2) (Fin 2) K) * Q = Q * N := by
      rw [hN_def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have h01 : N 0 1 = 0 := h g
    have hcol : N *ᵥ Pi.single 1 1 = N 1 1 • Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp [h01]
    rw [hw_def, mulVec_mulVec, hN, ← mulVec_mulVec, hcol, mulVec_smul]
  have hstab (g : G) (x : Fin 2 → K) (hx : x ∈ K ∙ w) :
      (ρ g : Matrix (Fin 2) (Fin 2) K) *ᵥ x ∈ K ∙ w := by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [mulVec_smul, hw, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  rcases hirr (K ∙ w) hstab with h0 | h1
  · have := congrFun (hQQ (Pi.single 1 1)) 1
    rw [← hw_def, Submodule.span_singleton_eq_bot.mp h0, mulVec_zero] at this
    simp at this
  · obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      (h1 ▸ Submodule.mem_top : (Q : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 1 ∈ K ∙ w)
    have := congrFun (congrArg ((↑Q⁻¹ : Matrix (Fin 2) (Fin 2) K) *ᵥ ·) hr) 0
    simp only [hw_def, mulVec_smul, hQQ] at this
    simp at this

variable [FaithfulSMul A K]

/-- A `2 × 2` matrix whose characteristic polynomial is integral with residually distinct roots
`u ≠ v` is conjugate to a diagonal matrix whose entries are integral, with residues `u` and `v`. -/
private theorem exists_conj_eq_diagonal [HenselianRing A (maximalIdeal A)]
    {M : Matrix (Fin 2) (Fin 2) K} {P : A[X]} {u v : ResidueField A} (huv : u ≠ v)
    (hP : P.map (algebraMap A K) = M.charpoly)
    (hPr : P.map (residue A) = (X - C u) * (X - C v)) :
    ∃ (Q : (Matrix (Fin 2) (Fin 2) K)ˣ) (α β : A),
      ((Q⁻¹ : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K) * M * Q =
        diagonal ![algebraMap A K α, algebraMap A K β] ∧
      residue A α = u ∧ residue A β = v := by
  have hinj := FaithfulSMul.algebraMap_injective A K
  have hmon : P.Monic := monic_of_injective hinj (hP ▸ charpoly_monic M)
  -- Hensel's lemma lifts the residually simple roots `u` and `v` of `P`.
  have hroot {u v : ResidueField A} (huv : u ≠ v)
      (hPr : P.map (residue A) = (X - C u) * (X - C v)) :
      ∃ α : A, P.IsRoot α ∧ residue A α = u := by
    obtain ⟨a₀, rfl⟩ := residue_surjective u
    obtain ⟨α, hα, hα'⟩ := HenselianRing.is_henselian P hmon a₀
      (by rw [← residue_eq_zero_iff, ← eval_map_apply, hPr]; simp)
      (by
        -- `Ideal.Quotient.mk (maximalIdeal A)` is `residue A` by definition
        change IsUnit (residue A _)
        rw [← eval_map_apply, ← derivative_map, hPr]
        simpa [derivative_mul, sub_eq_zero] using huv)
    exact ⟨α, hα, by rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]⟩
  obtain ⟨α, hα, hαu⟩ := hroot huv hPr
  obtain ⟨β, hβ, hβv⟩ := hroot huv.symm (by rw [hPr, mul_comm])
  have heig (γ : A) (hγ : P.IsRoot γ) :
      ∃ w, Module.End.HasEigenvector (toLin' M) (algebraMap A K γ) w :=
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr (by
      rw [IsRoot, Matrix.charpoly_toLin', ← hP, eval_map_apply, hγ.eq_zero, map_zero])
      ).exists_hasEigenvector
  obtain ⟨w₁, hw₁⟩ := heig α hα
  obtain ⟨w₂, hw₂⟩ := heig β hβ
  have hMw₁ : M *ᵥ w₁ = algebraMap A K α • w₁ := hw₁.apply_eq_smul
  have hMw₂ : M *ᵥ w₂ = algebraMap A K β • w₂ := hw₂.apply_eq_smul
  have hαβ : algebraMap A K α ≠ algebraMap A K β := fun h => huv (by rw [← hαu, ← hβv, hinj h])
  set Q₀ : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => ![w₁, w₂] j i
  have hli : LinearIndependent K Q₀.col := by
    rw [show Q₀.col = ![w₁, w₂] by ext j i; fin_cases j <;> rfl]
    refine Module.End.eigenvectors_linearIndependent' (toLin' M)
      ![algebraMap A K α, algebraMap A K β] ?_ _ (Fin.forall_fin_two.mpr ⟨hw₁, hw₂⟩)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hQ : IsUnit Q₀ := linearIndependent_col_iff_isUnit.mp hli
  refine ⟨hQ.unit, α, β, ?_, hαu, hβv⟩
  have hMQ : M * Q₀ = Q₀ * diagonal ![algebraMap A K α, algebraMap A K β] := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_diagonal, Fin.sum_univ_two]
    fin_cases j
    · simpa [Q₀, mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using congrFun hMw₁ i
    · simpa [Q₀, mulVec, dotProduct, Fin.sum_univ_two, mul_comm] using congrFun hMw₂ i
  rw [Matrix.mul_assoc, hQ.unit_spec, hMQ, ← Matrix.mul_assoc, hQ.val_inv_mul, Matrix.one_mul]

omit [IsLocalRing A] in
/-- A homomorphism to `GL₂(K)` whose matrices have integral entries lifts to `GL₂(A)`. -/
private theorem exists_lift_mapMatrix (N : G →* (Matrix (Fin 2) (Fin 2) K)ˣ)
    (hN : ∀ g i j, ∃ x : A, algebraMap A K x = (N g : Matrix (Fin 2) (Fin 2) K) i j) :
    ∃ ρA : G →* (Matrix (Fin 2) (Fin 2) A)ˣ, ∀ g i j,
      algebraMap A K ((ρA g : Matrix (Fin 2) (Fin 2) A) i j) =
        (N g : Matrix (Fin 2) (Fin 2) K) i j := by
  choose x hx using hN
  let f : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) K := (algebraMap A K).mapMatrix
  have hf : Function.Injective f := Matrix.map_injective (FaithfulSMul.algebraMap_injective A K)
  have hfx (g : G) : f (Matrix.of (x g)) = N g := by ext i j; exact hx g i j
  let ρ' : G →* Matrix (Fin 2) (Fin 2) A :=
    { toFun g := Matrix.of (x g)
      map_one' := hf (by rw [hfx, map_one, map_one, Units.val_one])
      map_mul' g h := hf (by rw [map_mul, hfx, hfx, hfx, map_mul, Units.val_mul]) }
  exact ⟨ρ'.toHomUnits, hx⟩

/-- Conjugating by `diag(1, c⁻¹)` multiplies the upper right entry of a `2 × 2` matrix by `c⁻¹`
and the lower left entry by `c`. -/
private theorem exists_conj_eq_scale {c : K} (hc : c ≠ 0) :
    ∃ D : (Matrix (Fin 2) (Fin 2) K)ˣ, ∀ M : Matrix (Fin 2) (Fin 2) K,
      (↑D⁻¹ : Matrix (Fin 2) (Fin 2) K) * M * D = !![M 0 0, M 0 1 * c⁻¹; c * M 1 0, M 1 1] := by
  refine ⟨⟨diagonal ![1, c⁻¹], diagonal ![1, c], ?_, ?_⟩, fun M => ?_⟩
  · rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; fin_cases i <;> simp [hc]
  · rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; fin_cases i <;> simp [hc]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal_mul, mul_diagonal]
    field_simp

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
  obtain ⟨D, hD⟩ := exists_conj_eq_scale hb₁
  set N' := (MulAut.conj D⁻¹).toMonoidHom.comp N
  have hN' (g : G) : (N' g : Matrix (Fin 2) (Fin 2) K) =
      (↑D⁻¹ : Matrix (Fin 2) (Fin 2) K) * N g * D := by
    simp only [N', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Units.val_mul]
  have hint (g : G) (i j : Fin 2) :
      ∃ z : A, algebraMap A K z = (N' g : Matrix (Fin 2) (Fin 2) K) i j := by
    rw [hN', hD]
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, of_apply,
      cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    · exact ⟨x g, hx g⟩
    · refine hA _ ?_
      rw [norm_mul, norm_inv]
      exact mul_inv_le_one_of_le₀ (hg₁ g) (norm_nonneg _)
    · exact ⟨x (g₁ * g) - x g₁ * x g, (hbc g₁ g).symm⟩
    · exact ⟨y g, hy g⟩
  obtain ⟨ρA, hρA⟩ := exists_lift_mapMatrix N' hint
  have hρA' (g : G) (i j : Fin 2) : algebraMap A K ((ρA g : Matrix (Fin 2) (Fin 2) A) i j) =
      !![(N g : Matrix (Fin 2) (Fin 2) K) 0 0, (N g : Matrix (Fin 2) (Fin 2) K) 0 1 * b₁⁻¹;
        b₁ * (N g : Matrix (Fin 2) (Fin 2) K) 1 0, (N g : Matrix (Fin 2) (Fin 2) K) 1 1] i j := by
    rw [hρA, hN', hD]
  refine ⟨D, ρA, fun g i j => (hρA g i j).trans (by rw [hN']), fun g => ⟨?_, ?_, ?_⟩, ?_⟩
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
  obtain ⟨Q₀, α, β, hQ₀, hα, hβ⟩ := exists_conj_eq_diagonal hg₀ (hP g₀) (hPr g₀)
  set N₀ : G →* (Matrix (Fin 2) (Fin 2) K)ˣ := (MulAut.conj Q₀⁻¹).toMonoidHom.comp ρ
  have hN₀ (g : G) : (N₀ g : Matrix (Fin 2) (Fin 2) K) =
      (↑Q₀⁻¹ : Matrix (Fin 2) (Fin 2) K) * ρ g * Q₀ := by
    simp only [N₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      Units.val_mul]
  have htr (g : G) : ∃ t : A, algebraMap A K t = (N₀ g : Matrix (Fin 2) (Fin 2) K).trace ∧
      residue A t = χ g + ψ g := by
    rw [hN₀, trace_mul_cycle, Units.mul_inv, Matrix.one_mul]
    exact exists_algebraMap_eq_trace (hP g) (hPr g)
  choose x y hx hy hxr hyr using
    exists_diagonal_entries N₀ χ ψ htr (hN₀ g₀ ▸ hQ₀) hα hβ hg₀
  -- Choose `g₁` maximizing the norm of the upper right entry; it is nonzero by irreducibility.
  obtain ⟨g', hg'⟩ := exists_conj_apply_zero_one_ne_zero ρ hirr Q₀
  have hcont : Continuous fun g => ‖(N₀ g : Matrix (Fin 2) (Fin 2) K) 0 1‖ := by
    simp only [hN₀]
    exact ((continuous_const.matrix_mul hρ).matrix_mul continuous_const).matrix_elem 0 1 |>.norm
  obtain ⟨g₁, -, hg₁⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  have hb₁ : (N₀ g₁ : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 := norm_pos_iff.mp <|
    (norm_pos_iff.mpr (by rwa [← hN₀] at hg')).trans_le (hg₁ (Set.mem_univ g'))
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
