/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import TauCeti.Algebra.Cellular.Simple

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Semisimplicity of cellular algebras and the split Wedderburn decomposition

Graham and Lehrer prove that a cellular algebra over a field with finite cell poset is semisimple
if and only if every cell form is nondegenerate (equivalently, every cell radical vanishes, or
every Gram matrix has nonzero determinant). Moreover, whenever all Gram determinants are units over
an arbitrary commutative base ring `R`, the bundled product of cell representations gives an
explicit `R`-algebra isomorphism

`A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`,

realizing `A` as a split direct product of matrix algebras over `R`.

This file establishes both the ring-general split Wedderburn isomorphism and Graham and Lehrer's
field-level semisimplicity criterion, together with the single-cell cellular structure on any
commutative ring `R` and the `ℤ` counterexample showing that neither Graham–Lehrer theorem over a
field extends to arbitrary commutative base rings:

* `TauCeti.CellularBasis.cellRepPiAlgEquiv`: when `Λ` is a finite partial order and
  `∀ μ, IsUnit (c.gramMatrix μ).det`, the product of cell representations
  `c.cellRepPi : A →ₐ[R] ∀ μ, Matrix (M μ) (M μ) R` is an `R`-algebra isomorphism;
* `TauCeti.CellularBasis.cellRadical_eq_bot_of_isSemisimpleRing`: over a field `K` (for any partial
  order `Λ`, without finiteness), semisimplicity of `B` forces every cell radical to vanish;
* `TauCeti.CellularBasis.isSemisimpleRing_iff_forall_cellRadical_eq_bot`,
  `TauCeti.CellularBasis.isSemisimpleRing_iff_forall_nondegenerate_cellForm`,
  `TauCeti.CellularBasis.isSemisimpleRing_iff_forall_det_gramMatrix_ne_zero`: Graham and Lehrer's
  semisimplicity equivalences over a field when `Λ` is finite;
* `TauCeti.CellularBasis.self R`: the single-cell cellular basis `{1}` of any commutative ring `R`,
  applied at `R = ℤ` to witness a nondegenerate cell form (`det = 1`) over a non-semisimple ring
  whose radical quotient is not simple.

## Main definitions

* `TauCeti.CellularBasis.cellRepPi c`: the product algebra homomorphism
  `A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`.
* `TauCeti.CellularBasis.cellRepPiAlgEquiv c h`: the `R`-algebra isomorphism
  `A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R` when every Gram determinant is a unit.
* `TauCeti.CellularBasis.self R`: the canonical single-cell cellular basis of a commutative ring
  `R` as an `R`-algebra.

## Main results

* `TauCeti.CellularBasis.cellRepPi_injective`, `TauCeti.CellularBasis.cellRepPi_surjective`:
  bijectivity of `cellRepPi` when every Gram determinant is a unit.
* `TauCeti.CellularBasis.isSemisimpleRing_of_forall_isUnit_det_gramMatrix`: over a commutative
  semisimple base ring, unit Gram determinants imply `IsSemisimpleRing A`.
* `TauCeti.CellularBasis.isSemisimpleRing_iff_forall_nondegenerate_cellForm`: Graham and Lehrer's
  criterion over a field (`IsSemisimpleRing B ↔ ∀ μ, (d.cellForm μ).Nondegenerate`).
* `TauCeti.CellularBasis.isSimpleModule_cellModule_iff_nonempty`,
  `TauCeti.CellularBasis.existsUnique_cellModule_linearEquiv`: when `B` is semisimple over a field,
  the nonempty cell modules themselves form a complete, irredundant list of simple `B`-modules.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Theorem 3.8.
-/

public section

open Module Submodule
open scoped Matrix

namespace TauCeti.CellularBasis

section SplitWedderburn

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]

section Preorder

variable [Preorder Λ] (c : CellularBasis R A M)

/-- The bundled `R`-algebra homomorphism sending `a : A` to its tuple of cell representations
`fun μ => c.cellRep μ a`. -/
noncomputable def cellRepPi : A →ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R :=
  AlgHom.pi c.cellRep

/-- Evaluating `c.cellRepPi a` at `μ` yields `c.cellRep μ a`. -/
@[simp]
theorem cellRepPi_apply (a : A) (μ : Λ) : c.cellRepPi a μ = c.cellRep μ a := (rfl)

end Preorder

section PartialOrder

variable [PartialOrder Λ] (c : CellularBasis R A M)

/-- When `Λ` is a finite partial order and every Gram matrix has invertible determinant, the
bundled cell representation `c.cellRepPi` is injective. -/
theorem cellRepPi_injective [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det) :
    Function.Injective c.cellRepPi := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha_ne
  have : Fintype Λ := Fintype.ofFinite Λ
  have : DecidableEq Λ := Classical.decEq Λ
  let P : Set Λ := {ν | ∃ s t : M ν, c.basis.repr a ⟨ν, s, t⟩ ≠ 0}
  have hP : P.Nonempty := by
    rw [Set.nonempty_def]
    by_contra! hP0
    have hall (i : Σ ν, M ν × M ν) : c.basis.repr a i = 0 := by
      by_contra hne
      exact hP0 i.1 ⟨i.2.1, i.2.2, hne⟩
    apply ha_ne
    rw [← c.basis.sum_repr a]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hall i, zero_smul]
  obtain ⟨μ, ⟨s₀, t₀, hne₀⟩, hmax⟩ := (Set.toFinite P).exists_maximal hP
  have hμ_zero : c.cellRep μ a = 0 := congrFun ha μ
  have hother (ν : Λ) (hν : ν ≠ μ) (s t : M ν) :
      c.basis.repr a ⟨ν, s, t⟩ • c.cellRep μ (c.basis ⟨ν, s, t⟩) = 0 := by
    by_cases hc : c.basis.repr a ⟨ν, s, t⟩ = 0
    · rw [hc, zero_smul]
    · have hnotle : ¬ μ ≤ ν := fun hle => hν (le_antisymm (hmax ⟨s, t, hc⟩ hle) hle)
      rw [c.cellRep_basis_of_not_le hnotle, smul_zero]
  have hsum_μ : ∑ p : M μ × M μ,
      c.basis.repr a ⟨μ, p.1, p.2⟩ • c.cellRep μ (c.basis ⟨μ, p.1, p.2⟩) = 0 := by
    have hexp : c.cellRep μ a = ∑ ν : Λ, ∑ p : M ν × M ν,
        c.basis.repr a ⟨ν, p.1, p.2⟩ • c.cellRep μ (c.basis ⟨ν, p.1, p.2⟩) := by
      conv_lhs => rw [← c.basis.sum_repr a]
      rw [map_sum, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul]
    rw [hμ_zero, Fintype.sum_eq_single μ fun ν hν =>
      Finset.sum_eq_zero fun p _ => hother ν hν p.1 p.2] at hexp
    exact hexp.symm
  let X : Matrix (M μ) (M μ) R := Matrix.of fun s t => c.basis.repr a ⟨μ, s, t⟩
  have hXG : X * c.gramMatrix μ = 0 := by
    ext w u
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have hentry := congrFun (congrFun hsum_μ w) u
    simp only [Matrix.sum_apply, Matrix.smul_apply, c.cellRep_basis, smul_eq_mul, mul_ite, mul_zero,
      Fintype.sum_prod_type, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Matrix.zero_apply] at hentry
    simpa [X] using hentry
  have hX : X = 0 := by
    calc
      X = X * (c.gramMatrix μ * (c.gramMatrix μ)⁻¹) := by
        rw [Matrix.mul_nonsing_inv _ (h μ), Matrix.mul_one]
      _ = (X * c.gramMatrix μ) * (c.gramMatrix μ)⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [hXG, Matrix.zero_mul]
  exact hne₀ (congrFun (congrFun hX s₀) t₀)

/-- When `Λ` is a finite partial order and every Gram matrix has invertible determinant, the
bundled cell representation `c.cellRepPi` is surjective. -/
theorem cellRepPi_surjective [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det) :
    Function.Surjective c.cellRepPi := by
  have : Fintype Λ := Fintype.ofFinite Λ
  have : DecidableEq Λ := Classical.decEq Λ
  have : DecidableRel (· ≤ · : Λ → Λ → Prop) := Classical.decRel _
  have : DecidableRel (· < · : Λ → Λ → Prop) := Classical.decRel _
  let rk (μ : Λ) : ℕ := (Finset.univ.filter (· ≤ μ)).card
  have hrk_lt {ν μ : Λ} (hν : ν < μ) : rk ν < rk μ := by
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · intro τ hτ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hτ).2.trans hν.le⟩
    · intro heq
      have hmem : μ ∈ Finset.univ.filter (· ≤ ν) :=
        heq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
      exact not_le_of_gt hν (Finset.mem_filter.mp hmem).2
  have hsingle (n : ℕ) : ∀ μ : Λ, rk μ = n → ∀ (w v : M μ) (r : R),
      Pi.single μ (Matrix.single w v r) ∈ c.cellRepPi.range := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rintro μ rfl w v r
      let x : A := ∑ t : M μ, (r * (c.gramMatrix μ)⁻¹ v t) • c.basis ⟨μ, w, t⟩
      have hx_le : x ∈ c.leSpan μ :=
        sum_mem fun t _ => smul_mem _ _ (c.basis_self_mem_leSpan μ w t)
      have hx_diag : c.cellRep μ x = Matrix.single w v r := by
        ext u s
        have hinv := congrFun (congrFun (Matrix.nonsing_inv_mul _ (h μ)) v) s
        simp only [Matrix.mul_apply, Matrix.one_apply] at hinv
        simp only [x, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, c.cellRep_basis,
          smul_eq_mul, Matrix.single_apply]
        by_cases hu : u = w
        · subst hu
          simp only [↓reduceIte, true_and, mul_assoc, ← Finset.mul_sum, hinv, mul_ite, mul_one,
            mul_zero]
        · have hwu : w ≠ u := Ne.symm hu
          simp [hu, hwu]
      have hdiff : c.cellRepPi x - Pi.single μ (Matrix.single w v r) =
          ∑ ν ∈ Finset.univ.filter (· < μ), ∑ a : M ν, ∑ b : M ν,
            Pi.single ν (Matrix.single a b (c.cellRep ν x a b)) := by
        ext τ i j
        rw [Pi.sub_apply, cellRepPi_apply, Finset.sum_apply, Matrix.sum_apply]
        by_cases hτμ : τ = μ
        · subst hτμ
          rw [hx_diag, Pi.single_eq_same, sub_self, Matrix.zero_apply]
          symm
          refine Finset.sum_eq_zero fun ν hν => ?_
          have hne : τ ≠ ν := ne_of_gt (Finset.mem_filter.mp hν).2
          simp [Finset.sum_apply, Pi.single_eq_of_ne hne]
        · rw [Pi.single_eq_of_ne hτμ, sub_zero]
          by_cases hlt : τ < μ
          · have hmem : τ ∈ Finset.univ.filter (· < μ) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
            rw [Finset.sum_eq_single τ
              (fun ν _ hν => by simp [Finset.sum_apply, Pi.single_eq_of_ne (Ne.symm hν)])
              (fun h => (h hmem).elim)]
            simp [Finset.sum_apply, Matrix.sum_apply, Pi.single_eq_same, Matrix.single_apply,
              ite_and]
          · have hnotle : ¬ τ ≤ μ := fun hle => hlt (lt_of_le_of_ne hle hτμ)
            rw [c.cellRep_eq_zero_of_mem_leSpan hnotle hx_le, Matrix.zero_apply]
            symm
            refine Finset.sum_eq_zero fun ν hν => ?_
            have hne : τ ≠ ν := fun h => hlt (h ▸ (Finset.mem_filter.mp hν).2)
            simp [Finset.sum_apply, Pi.single_eq_of_ne hne]
      have hlow_mem : c.cellRepPi x - Pi.single μ (Matrix.single w v r) ∈ c.cellRepPi.range := by
        rw [hdiff]
        exact sum_mem fun ν hν => sum_mem fun a _ => sum_mem fun b _ =>
          ih (rk ν) (hrk_lt (Finset.mem_filter.mp hν).2) ν rfl a b _
      have hx_mem : c.cellRepPi x ∈ c.cellRepPi.range := ⟨x, rfl⟩
      simpa using sub_mem hx_mem hlow_mem
  intro F
  have hF : F = ∑ μ : Λ, ∑ w : M μ, ∑ v : M μ, Pi.single μ (Matrix.single w v (F μ w v)) := by
    ext μ w v
    rw [Finset.sum_apply, Fintype.sum_eq_single μ
      (fun ν hν => by simp [Finset.sum_apply, Pi.single_eq_of_ne (Ne.symm hν)])]
    simp [Finset.sum_apply, Matrix.sum_apply, Pi.single_eq_same, Matrix.single_apply, ite_and]
  rw [hF]
  exact sum_mem fun μ _ => sum_mem fun w _ => sum_mem fun v _ => hsingle (rk μ) μ rfl w v (F μ w v)

/-- **Split Wedderburn decomposition of a cellular algebra**: when `Λ` is a finite partial order
and every Gram matrix has invertible determinant in `R`, the bundled cell representation is an
`R`-algebra isomorphism `A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R`. -/
noncomputable def cellRepPiAlgEquiv [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det) :
    A ≃ₐ[R] ∀ μ : Λ, Matrix (M μ) (M μ) R :=
  AlgEquiv.ofBijective c.cellRepPi ⟨c.cellRepPi_injective h, c.cellRepPi_surjective h⟩

/-- Evaluating `c.cellRepPiAlgEquiv h a` at `μ` yields `c.cellRep μ a`. -/
@[simp]
theorem cellRepPiAlgEquiv_apply [Finite Λ] (h : ∀ μ, IsUnit (c.gramMatrix μ).det) (a : A)
    (μ : Λ) : c.cellRepPiAlgEquiv h a μ = c.cellRep μ a := (rfl)

/-- Over a commutative semisimple base ring `R`, if `Λ` is a finite partial order and every Gram
matrix has invertible determinant, then `A` is a semisimple ring. -/
theorem isSemisimpleRing_of_forall_isUnit_det_gramMatrix [IsSemisimpleRing R] [Finite Λ]
    (h : ∀ μ, IsUnit (c.gramMatrix μ).det) : IsSemisimpleRing A :=
  (c.cellRepPiAlgEquiv h).toRingEquiv.symm.isSemisimpleRing

/-- Over a nontrivial commutative base ring, if `A` is a semisimple ring and `Λ` is a partial
order, then the Gram matrix of every nonempty cell is nonzero. -/
theorem gramMatrix_ne_zero_of_isSemisimpleRing [Nontrivial R] [IsSemisimpleRing A] (μ : Λ)
    [Nonempty (M μ)] : c.gramMatrix μ ≠ 0 := by
  intro h0
  obtain ⟨s₀⟩ := ‹Nonempty (M μ)›
  have hmul_lower {x y : A} (hx : x ∈ c.leSpan μ) (hy : y ∈ c.leSpan μ) :
      x * y ∈ c.lowerSpan μ := by
    rw [c.leSpan_def] at hx
    induction hx using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨⟨ν₁, s₁, t₁⟩, h₁ : ν₁ ≤ μ, rfl⟩ := hu
      by_cases hlt₁ : ν₁ < μ
      · exact c.mem_lowerSpan_mul y (c.basis_mem_lowerSpan hlt₁ s₁ t₁)
      · have hν₁ : ν₁ = μ := eq_of_le_of_not_lt h₁ hlt₁
        subst ν₁
        rw [c.leSpan_def] at hy
        induction hy using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨⟨ν₂, s₂, t₂⟩, h₂ : ν₂ ≤ μ, rfl⟩ := hv
          by_cases hlt₂ : ν₂ < μ
          · exact c.mul_mem_lowerSpan _ (c.basis_mem_lowerSpan hlt₂ s₂ t₂)
          · have hν₂ : ν₂ = μ := eq_of_le_of_not_lt h₂ hlt₂
            subst ν₂
            have hsub := c.basis_mul_basis_sub_mem μ s₁ t₁ s₂ t₂
            simpa [h0] using hsub
        | zero => simp
        | add v₁ v₂ _ _ ih₁ ih₂ => rw [mul_add]; exact add_mem ih₁ ih₂
        | smul r v _ ih =>
          rw [Algebra.smul_def, ← mul_assoc, ← Algebra.commutes r, mul_assoc, ← Algebra.smul_def]
          exact smul_mem _ r ih
    | zero => simp
    | add u₁ u₂ _ _ ih₁ ih₂ => rw [add_mul]; exact add_mem ih₁ ih₂
    | smul r u _ ih => rw [smul_mul_assoc]; exact smul_mem _ r ih
  let I : Ideal A :=
    { carrier := c.leSpan μ
      zero_mem' := (c.leSpan μ).zero_mem
      add_mem' := (c.leSpan μ).add_mem
      smul_mem' := fun a _ hx => c.mul_mem_leSpan a hx }
  obtain ⟨e, he_idem, he_span⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  have he_I : e ∈ I := he_span ▸ Ideal.subset_span (Set.mem_singleton e)
  have he_low : e ∈ c.lowerSpan μ := by
    rw [← he_idem.eq]
    exact hmul_lower he_I he_I
  have hbasis_I : c.basis ⟨μ, s₀, s₀⟩ ∈ I := c.basis_self_mem_leSpan μ s₀ s₀
  rw [he_span, Ideal.mem_span_singleton'] at hbasis_I
  obtain ⟨b, hb⟩ := hbasis_I
  have hbasis_low : c.basis ⟨μ, s₀, s₀⟩ ∈ c.lowerSpan μ := by
    rw [← hb]
    exact c.mul_mem_lowerSpan b he_low
  have h10 : (1 : R) = 0 := by
    simpa using c.mem_lowerSpan_iff.mp hbasis_low ⟨μ, s₀, s₀⟩ (lt_irrefl μ)
  exact one_ne_zero h10

end PartialOrder

end SplitWedderburn

section Field

variable {K B Λ : Type*} [Field K] [Ring B] [Algebra K B] [PartialOrder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (d : CellularBasis K B M)

/-- Over a field, if a cellular algebra `B` is semisimple, then every cell radical vanishes (no
finiteness assumption on the cell poset `Λ` is needed). -/
theorem cellRadical_eq_bot_of_isSemisimpleRing [IsSemisimpleRing B] (μ : Λ) :
    d.cellRadical μ = ⊥ := by
  rcases isEmpty_or_nonempty (M μ) with hempty | hne
  · have : Subsingleton (d.CellModule μ) := (d.cellModuleEquiv μ).toEquiv.subsingleton
    exact Subsingleton.elim _ _
  · have hgram : d.gramMatrix μ ≠ 0 := d.gramMatrix_ne_zero_of_isSemisimpleRing μ
    have hform : d.cellForm μ ≠ 0 := mt (d.cellForm_eq_zero_iff μ).mp hgram
    have hne_top : d.cellRadical μ ≠ ⊤ := mt (d.cellRadical_eq_top_iff μ).mp hform
    obtain ⟨N, hcompl⟩ := exists_isCompl (d.cellRadical μ)
    by_cases hN : N = ⊤
    · have hbot := hcompl.inf_eq_bot
      rwa [hN, inf_top_eq] at hbot
    · exfalso
      have hle : N ≤ d.cellRadical μ := d.le_cellRadical_of_ne_top μ N hN
      exact hne_top (eq_top_iff.mpr (hcompl.sup_eq_top ▸ sup_le le_rfl hle))

/-- Over a field, if a cellular algebra `B` is semisimple, then a cell module `d.CellModule μ` is
simple if and only if its index set `M μ` is nonempty. -/
theorem isSimpleModule_cellModule_iff_nonempty [IsSemisimpleRing B] (μ : Λ) :
    IsSimpleModule B (d.CellModule μ) ↔ Nonempty (M μ) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : Nontrivial (d.CellModule μ) := IsSimpleModule.nontrivial B _
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have : Subsingleton (d.CellModule μ) := (d.cellModuleEquiv μ).toEquiv.subsingleton
    exact false_of_nontrivial_of_subsingleton (d.CellModule μ)
  · have hform : d.cellForm μ ≠ 0 :=
      mt (d.cellForm_eq_zero_iff μ).mp (d.gramMatrix_ne_zero_of_isSemisimpleRing μ)
    exact (d.isSimpleModule_cellModule_iff_of_cellForm_ne_zero hform).mpr
      (d.cellRadical_eq_bot_of_isSemisimpleRing μ)

section Finite

variable [Finite Λ]

/-- **Graham–Lehrer semisimplicity criterion** (Theorem 3.8, radical form): over a field, a
cellular algebra with finite cell poset is semisimple if and only if every cell radical is
trivial. -/
theorem isSemisimpleRing_iff_forall_cellRadical_eq_bot :
    IsSemisimpleRing B ↔ ∀ μ, d.cellRadical μ = ⊥ :=
  ⟨fun _ μ => d.cellRadical_eq_bot_of_isSemisimpleRing μ,
    fun h => d.isSemisimpleRing_of_forall_isUnit_det_gramMatrix fun μ =>
      ((d.cellRadical_eq_bot_iff_det_gramMatrix_ne_zero μ).mp (h μ)).isUnit⟩

/-- **Graham–Lehrer semisimplicity criterion** (Theorem 3.8, bilinear-form form): over a field, a
cellular algebra with finite cell poset is semisimple if and only if every cell form is
nondegenerate. -/
theorem isSemisimpleRing_iff_forall_nondegenerate_cellForm :
    IsSemisimpleRing B ↔ ∀ μ, (d.cellForm μ).Nondegenerate := by
  simp_rw [d.isSemisimpleRing_iff_forall_cellRadical_eq_bot,
    d.nondegenerate_cellForm_iff_cellRadical_eq_bot]

/-- **Graham–Lehrer semisimplicity criterion** (Theorem 3.8, Gram-determinant form): over a field,
a cellular algebra with finite cell poset is semisimple if and only if every Gram matrix has
nonzero determinant. -/
theorem isSemisimpleRing_iff_forall_det_gramMatrix_ne_zero :
    IsSemisimpleRing B ↔ ∀ μ, (d.gramMatrix μ).det ≠ 0 := by
  simp_rw [d.isSemisimpleRing_iff_forall_cellRadical_eq_bot,
    d.cellRadical_eq_bot_iff_det_gramMatrix_ne_zero]

/-- Over a field, when `Λ` is a finite partial order and `B` is semisimple, every simple left
`B`-module is isomorphic to `d.CellModule μ` itself for a unique cell `μ : Λ`. -/
theorem existsUnique_cellModule_linearEquiv [IsSemisimpleRing B]
    (S : Type*) [AddCommGroup S] [Module B S] [IsSimpleModule B S] :
    ∃! μ : Λ, Nonempty (d.CellModule μ ≃ₗ[B] S) := by
  have heq (μ : Λ) :
      Nonempty (d.CellModule μ ≃ₗ[B] S) ↔
        Nonempty ((d.CellModule μ ⧸ d.cellRadical μ) ≃ₗ[B] S) := by
    have eq_bot := d.cellRadical_eq_bot_of_isSemisimpleRing μ
    let q := Submodule.quotEquivOfEqBot (d.cellRadical μ) eq_bot
    exact ⟨fun ⟨e⟩ => ⟨q.trans e⟩, fun ⟨e⟩ => ⟨q.symm.trans e⟩⟩
  simp_rw [heq]
  exact d.existsUnique_cellModule_quotient_linearEquiv S

end Finite

end Field

section Self

variable (R : Type*) [CommRing R]

/-- Any commutative ring `R` is cellular as an `R`-algebra with a single cell `()`, a singleton
index set `Unit`, basis `{1}`, and `AlgEquiv.toOpposite R R` as anti-involution. -/
noncomputable def self : CellularBasis R R (fun _ : Unit => Unit) where
  basis := (Basis.singleton Unit R).reindex
    ⟨fun _ => ⟨(), (), ()⟩, fun _ => (), fun ⟨⟩ => rfl, fun ⟨⟨⟩, ⟨⟩, ⟨⟩⟩ => rfl⟩
  antiInvolution := AlgEquiv.toOpposite R R
  unop_antiInvolution_basis _ _ _ := by simp
  exists_mul_basis a _ _ := ⟨fun _ => a, fun _ => by simp⟩

variable {R}

/-- The unique cellular basis vector of `self R` is `1`. -/
@[simp]
theorem self_basis (s t : Unit) : (self R).basis ⟨(), s, t⟩ = 1 := by
  simp [self]

/-- The strict lower span of the unique cell of `self R` is trivial. -/
@[simp]
theorem lowerSpan_self : (self R).lowerSpan () = ⊥ := by
  have h : {i : Σ _ : Unit, Unit × Unit | i.1 < ()} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ hi => lt_irrefl () hi
  rw [lowerSpan_def, h, Set.image_empty, Submodule.span_empty]

/-- In `self R`, every scalar `r : R` acts as the `1 × 1` matrix `(r)` on the unique cell. -/
@[simp]
theorem cellRep_self (r : R) (s t : Unit) : (self R).cellRep () r s t = r := by
  have h := (self R).mul_basis_sub_sum_mem r () () ()
  rw [lowerSpan_self, Submodule.mem_bot, sub_eq_zero] at h
  cases s
  cases t
  simpa using h.symm

/-- The Gram matrix of the unique cell of `self R` is the `1 × 1` identity matrix. -/
@[simp]
theorem gramMatrix_self : (self R).gramMatrix () = 1 := by
  ext s t
  cases s
  cases t
  simpa using ((self R).cellRep_basis () () () () ()).symm

/-- The Gram determinant of the unique cell of `self R` is `1`. -/
theorem det_gramMatrix_self : ((self R).gramMatrix ()).det = 1 := by
  simp

/-- The single-cell bilinear form of a commutative ring `R` is `(u, v) ↦ u () * v ()`, which is
nondegenerate over every commutative ring `R`. -/
theorem nondegenerate_cellForm_self : ((self R).cellForm ()).Nondegenerate := by
  have hsep : ((self R).cellForm ()).SeparatingLeft := by
    intro x hx
    apply ((self R).cellModuleEquiv ()).injective
    ext ⟨⟩
    simpa [cellForm_apply, Matrix.mulVec, dotProduct] using hx ((self R).cellBasis () ())
  exact ⟨hsep, fun y hy => hsep y fun x => by
    rw [((self R).isSymm_cellForm ()).eq]
    exact hy x⟩

/-- The cell radical of `self R` is trivial over every commutative ring `R`. -/
theorem cellRadical_self : (self R).cellRadical () = ⊥ :=
  ((self R).nondegenerate_cellForm_iff_cellRadical_eq_bot ()).mp nondegenerate_cellForm_self

private theorem nonempty_cellModule_quotient_addEquiv {R A Λ : Type*} [CommRing R] [Ring A]
    [Algebra R A] [Preorder Λ] {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
    (c : CellularBasis R A M) {μ : Λ} (h : c.cellRadical μ = ⊥) :
    Nonempty ((c.CellModule μ ⧸ c.cellRadical μ) ≃+ (M μ → R)) :=
  ⟨(Submodule.quotEquivOfEqBot (c.cellRadical μ) h).toAddEquiv.trans
    (c.cellModuleEquiv μ).toAddEquiv⟩

/-!
### Non-generalizability over arbitrary commutative rings

Neither Graham–Lehrer's simple-module classification nor their semisimplicity criterion holds over
an arbitrary commutative base ring: `CellularBasis.self ℤ` has a single cell whose form
`(u, v) ↦ uv` is nondegenerate (`det = 1` and `cellRadical = ⊥`), yet `ℤ` is not a semisimple ring
and the cell quotient `(self ℤ).CellModule () ⧸ (self ℤ).cellRadical ()` is not a simple `ℤ`-module.
-/
example :
    ((self ℤ).cellForm ()).Nondegenerate ∧
      ((self ℤ).gramMatrix ()).det = 1 ∧
      ¬ IsSemisimpleRing ℤ ∧
      ∀ [Module ℤ ((self ℤ).CellModule () ⧸ (self ℤ).cellRadical ())],
        ¬ IsSimpleModule ℤ ((self ℤ).CellModule () ⧸ (self ℤ).cellRadical ()) := by
  refine ⟨nondegenerate_cellForm_self, det_gramMatrix_self, ?_, ?_⟩
  · intro hss
    obtain ⟨e, he_idem, he_span⟩ :=
      IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {(2 : ℤ)})
    have he01 : e = 0 ∨ e = 1 := by
      have hmul : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he_idem.eq, sub_self]
      rcases mul_eq_zero.mp hmul with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h1)
    have h2mem : (2 : ℤ) ∈ Ideal.span {e} := he_span ▸ Ideal.subset_span (Set.mem_singleton _)
    rw [Ideal.mem_span_singleton'] at h2mem
    rcases he01 with rfl | rfl
    · obtain ⟨b, hb⟩ := h2mem
      omega
    · have h1mem : (1 : ℤ) ∈ Ideal.span {(2 : ℤ)} := by
        rw [he_span]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [Ideal.mem_span_singleton'] at h1mem
      obtain ⟨b, hb⟩ := h1mem
      omega
  · intro instM hsimple
    obtain ⟨e₀⟩ := nonempty_cellModule_quotient_addEquiv (self ℤ) cellRadical_self
    let e := e₀.trans (LinearEquiv.funUnique Unit ℤ ℤ).toAddEquiv
    let Q := (self ℤ).CellModule () ⧸ (self ℤ).cellRadical ()
    let dbl : Q →ₗ[ℤ] Q := LinearMap.id + LinearMap.id
    let N : Submodule ℤ Q := LinearMap.range dbl
    let v : Q := e.symm 1
    rcases eq_bot_or_eq_top N with hbot | htop
    · have hv_mem : dbl v ∈ (⊥ : Submodule ℤ Q) := hbot ▸ ⟨v, rfl⟩
      have hv_zero : v + v = 0 := (Submodule.mem_bot ℤ).mp hv_mem
      have h20 : (1 : ℤ) + 1 = 0 := by
        simpa [v, map_add] using congrArg e hv_zero
      omega
    · have hv_top : v ∈ N := htop.symm ▸ Submodule.mem_top
      obtain ⟨q, hq⟩ := hv_top
      have h21 : e q + e q = 1 := by
        simpa [dbl, v, map_add] using congrArg e hq
      omega

end Self

end TauCeti.CellularBasis
