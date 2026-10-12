/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Generated

/-!
# Graded Nakayama and detection of generating degrees

For a bounded-below internally graded module, the positive-degree part of the algebra cannot
surject onto the whole module unless the module is zero. More generally, homogeneous generators
modulo the positive-degree action generate the module itself. In particular, over a nonnegatively
graded algebra, a bounded-below module is generated in degree `d` exactly when every homogeneous
piece outside degree `d` lies in `A₊ M`.

The last criterion expresses concentration of `M / A₊ M` in degree `d` without choosing a
presentation of that quotient. It detects the generating degrees of terms of minimal graded
projective resolutions: maps to modules annihilated by `A₊` see precisely this quotient.
Neither projectivity nor semisimplicity is needed for the generation criterion. Boundedness below
is essential; no finite-generation hypothesis is required when a lower bound is supplied.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of graded rings*, Section 2.3, for graded modules.
* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for detection of linearity via the generating degrees of minimal resolutions.
-/

public section

namespace TauCeti.InternalGrading

open _root_.DirectSum

universe uk uA uM

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝒜 : ℤ → Submodule k A) {G : InternalGrading k M} [SetLike.GradedSMul 𝒜 G.piece]

/-- A component of `A₊ M` lies in an `A`-submodule if all lower-degree pieces do. The positive
scalar lowers the degree of the module component needed to compute that component. -/
theorem decompose_mem_of_mem_positive_smul_top (U : Submodule A M) {p : ℤ}
    (hU : ∀ q < p, ∀ x ∈ G.piece q, x ∈ U) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    (decompose G.piece x p : M) ∈ U := by
  classical
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · refine Submodule.iSup_induction _ (motive := fun a =>
      (decompose G.piece (a • y) p : M) ∈ U) ha (fun i a ha => ?_) ?_ ?_
    · refine Submodule.iSup_induction _ (motive := fun a =>
        (decompose G.piece (a • y) p : M) ∈ U) ha (fun hi a ha => ?_) ?_ ?_
      · let f : M →ₗ[k] M := Algebra.lsmul k k M a
        have hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece i :=
          TauCeti.LinearMap.isHomogeneous_def.mpr fun q z hz => by
            simpa [f, add_comm] using SetLike.GradedSMul.smul_mem ha hz
        have h := hf.map_decompose (p - i) y
        rw [sub_add_cancel] at h
        simpa only [f, Algebra.lsmul_apply] using
          h ▸ U.smul_mem a (hU (p - i) (by omega) _ (decompose G.piece y (p - i)).property)
      · simp
      · intro a b ha hb
        simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          U.add_mem ha hb
    · simp
    · intro a b ha hb
      simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
        U.add_mem ha hb
  · simpa only [decompose_add, DirectSum.add_apply, Submodule.coe_add] using U.add_mem hx hy

/-- **Graded Nakayama for homogeneous generators.** In a bounded-below graded module, if each
homogeneous piece lies in the sum of a homogeneous `A`-submodule and the positive-degree action
on the module, then that submodule is the whole module. This is generation modulo `A₊`. -/
theorem eq_top_of_piece_le_sup_positive_smul_top (U : Submodule A M)
    (hhom : SetLike.IsHomogeneous G.piece U) (b : ℤ)
    (hbelow : ∀ p < b, G.piece p = ⊥)
    (hU : ∀ p, G.piece p ≤ U.restrictScalars k ⊔
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) : U = ⊤ := by
  have pieces : ∀ n : ℕ, ∀ x ∈ G.piece (b + n), x ∈ U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hU _ hx)
      have lower : ∀ q < b + n, ∀ x ∈ G.piece q, x ∈ U := by
        intro q hq x hx
        by_cases hqb : q < b
        · rw [hbelow q hqb] at hx
          have hz : x = 0 := by simpa using hx
          rw [hz]
          exact U.zero_mem
        · have heq : b + (q - b).toNat = q := by omega
          exact ih (q - b).toNat (by omega) x (heq.symm ▸ hx)
      rw [← decompose_of_mem_same G.piece hx, decompose_add,
        DirectSum.add_apply, Submodule.coe_add]
      exact U.add_mem (hhom _ hy)
        (decompose_mem_of_mem_positive_smul_top 𝒜 U lower hz)
  apply top_unique
  intro x _
  classical
  rw [← sum_support_decompose G.piece x]
  refine U.sum_mem fun p _ => ?_
  by_cases hp : p < b
  · have hz := (Submodule.eq_bot_iff _).mp (hbelow p hp) _ (decompose G.piece x p).property
    rw [hz]
    exact U.zero_mem
  · have heq : b + (p - b).toNat = p := by omega
    exact pieces (p - b).toNat _ (heq.symm ▸ (decompose G.piece x p).property)

/-- **Graded Nakayama.** A bounded-below graded module satisfying `A₊ M = M` is zero. -/
theorem subsingleton_of_positive_smul_top_eq_top (b : ℤ)
    (hbelow : ∀ p < b, G.piece p = ⊥)
    (h : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) = ⊤) :
    Subsingleton M := by
  have hbot : (⊥ : Submodule A M) = ⊤ :=
    eq_top_of_piece_le_sup_positive_smul_top 𝒜 ⊥ (by
      intro p x hx
      have hx : x = 0 := by simpa using hx
      simp [hx]) b hbelow (by simp [h])
  exact subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊥ : Submodule A M) := hbot.symm ▸ Submodule.mem_top
    simpa using hx

variable [GradedAlgebra 𝒜]

/-- A bounded-below module over a nonnegatively graded algebra is generated in degree `d`
exactly when its homogeneous pieces outside degree `d` lie in `A₊ M`. Equivalently, its quotient
by the positive-degree action is concentrated in degree `d`. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  constructor
  · intro hG p hp
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · simp [hG.piece_eq_bot_of_lt 𝒜 h𝒜 hlt]
    · exact hG.piece_le_smul_top 𝒜 hgt
  · intro hG
    have hspan := eq_top_of_piece_le_sup_positive_smul_top 𝒜
      (Submodule.span A (G.piece d : Set M)) (isHomogeneous_span_piece 𝒜 d) b hbelow
      fun p => by
        by_cases hp : p = d
        · subst p
          exact le_sup_of_le_left fun x hx => Submodule.subset_span hx
        · exact le_sup_of_le_right (hG p hp)
    exact (G.isGeneratedInDegree_iff d).mpr fun x => hspan.symm ▸ Submodule.mem_top

/-- The generating-degree criterion for a module finite over the grading's scalar semiring.
Its internal grading has finite support, which supplies the lower bound automatically. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top_of_finite [Module.Finite k M]
    (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  obtain ⟨b, hb⟩ := G.finite_piece_ne_bot.bddBelow
  apply isGeneratedInDegree_iff_piece_le_positive_smul_top 𝒜 h𝒜 b _ d
  intro p hp
  by_contra hne
  have := hb hne
  omega

end TauCeti.InternalGrading
