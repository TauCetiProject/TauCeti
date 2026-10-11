/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Torsion
public import TauCeti.LinearAlgebra.LinearIndependent.Polynomial

/-!
# Homogeneous bases of the free part of a graded `k[X]`-module

Let `k` be a field and `M` a finitely generated `k[X]`-module with an internal `ℤ`-grading on
which `X` lowers degree by a fixed nonzero `d`. This file shows that the free part of `M` is
graded free: every homogeneous `k[X]`-submodule meeting the torsion submodule trivially has a
`k[X]`-basis of homogeneous elements. Together with the homogeneous complement to torsion of
`TauCeti.Algebra.Module.GradedModule.Torsion`, this gives the "tower" half of the structure theorem
for finitely generated graded `k[X]`-modules: `M` is the direct sum of its torsion submodule and a
free module on homogeneous generators, one `X`-tower per generator. The decomposition of the
torsion submodule into homogeneous cyclic summands is not treated here.

The basis is assembled degree by degree. In degree `p`, the degree-`p` part of the submodule
contains `X` times its degree-`(p + d)` part, and a `k`-basis of a complement is chosen. Since
degrees are bounded above, a form of graded Nakayama shows that these elements span. Since `X` is a
nonzerodivisor on the submodule, a relation among them could be divided by `X` indefinitely, so
they are linearly independent.

## Main results

* `TauCeti.InternalGrading.exists_linearIndependent_span_eq_of_disjoint_torsion`: a homogeneous
  submodule meeting torsion trivially is spanned by a linearly independent homogeneous family.
* `TauCeti.InternalGrading.exists_homogeneous_basis`: a torsion-free module has a homogeneous
  basis.
* `TauCeti.InternalGrading.exists_linearIndependent_isCompl_torsion`: the torsion submodule has a
  complement with a homogeneous basis.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Appendix A: the structure of finitely generated graded modules over
  `𝔽[U]`.
-/

public section

open Polynomial

namespace TauCeti.InternalGrading

universe u

variable {k : Type*} {M : Type u} [Field k] [AddCommGroup M] [Module k M] [Module k[X] M]
  [IsScalarTower k k[X] M] [Module.Finite k[X] M] {G : InternalGrading k M} {d : ℕ}

/-- **Homogeneous bases of the free part.** Let `X` lower degree by `d ≠ 0` in a finitely
generated graded `k[X]`-module over a field. Then a homogeneous `k[X]`-submodule `L` meeting the
torsion submodule trivially is the span of a `k[X]`-linearly independent family of homogeneous
elements. That is, `L` is graded free. -/
theorem exists_linearIndependent_span_eq_of_disjoint_torsion (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d))
    (L : Submodule k[X] M) (hL : DirectSum.SetLike.IsHomogeneous G.piece L)
    (hLT : Disjoint L (Submodule.torsion k[X] M)) :
    ∃ (ι : Type u) (b : ι → M) (deg : ι → ℤ), (∀ i, b i ∈ G.piece (deg i)) ∧
      LinearIndependent k[X] b ∧ Submodule.span k[X] (Set.range b) = L := by
  classical
  -- `V p` is the degree-`p` part of `L`, and `W p ≤ V p` is `X` times its degree-`(p + d)` part.
  let V : ℤ → Submodule k M := fun p ↦ G.piece p ⊓ L.restrictScalars k
  let W : ℤ → Submodule k M := fun p ↦
    (V (p + d)).map ((_root_.LinearMap.lsmul k[X] M X).restrictScalars k)
  have hWV (p : ℤ) : W p ≤ V p := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyG, hyL⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨?_, L.smul_mem X hyL⟩
    simpa using hX hyG
  -- Choose a complement `C p` of `W p` inside `V p`, and a `k`-basis `s p` of it.
  have hC (p : ℤ) : ∃ C : Submodule k M, C ≤ V p ∧ Disjoint (W p) C ∧ W p ⊔ C = V p := by
    obtain ⟨C', hC'⟩ := exists_isCompl (W p)
    refine ⟨C' ⊓ V p, inf_le_right, hC'.disjoint.mono_right inf_le_left, ?_⟩
    rw [← sup_inf_assoc_of_le C' (hWV p), hC'.sup_eq_top, top_inf_eq]
  choose C hCV hWC hWCV using hC
  choose s hsC hspan hli using fun p ↦ exists_linearIndependent k (C p : Set M)
  have hspan' (p : ℤ) : Submodule.span k (s p) = C p := by rw [hspan p, Submodule.span_eq]
  -- The family `b` collects the bases `s p` of all degrees.
  let b : (Σ p : ℤ, s p) → M := fun i ↦ i.2
  have hbC (i : Σ p : ℤ, s p) : b i ∈ C i.1 := hsC i.1 i.2.2
  have hbG (i : Σ p : ℤ, s p) : b i ∈ G.piece i.1 := (Submodule.mem_inf.mp (hCV _ (hbC i))).1
  have hspanL : Submodule.span k[X] (Set.range b) ≤ L :=
    Submodule.span_le.mpr fun _ ⟨i, hi⟩ ↦ hi ▸ (Submodule.mem_inf.mp (hCV _ (hbC i))).2
  -- Every component of an element of the `k`-span of `b` lies in the matching `C p`.
  have hcomp {z : M} (hz : z ∈ Submodule.span k (Set.range b)) (p : ℤ) :
      (DirectSum.decompose G.piece z p : M) ∈ C p := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      by_cases hi : i.1 = p
      · rw [DirectSum.decompose_of_mem_same _ (hi ▸ hbG i)]
        exact hi ▸ hbC i
      · rw [DirectSum.decompose_of_mem_ne _ (hbG i) hi]
        exact (C p).zero_mem
    | zero => simp
    | add x y _ _ hx hy => simpa using (C p).add_mem hx hy
    | smul a x _ hx =>
      rw [DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]
      exact (C p).smul_mem a hx
  refine ⟨Σ p : ℤ, s p, b, fun i ↦ i.1, hbG, ?_, ?_⟩
  · refine LinearIndependent.polynomial ?_ (fun x hx hXx ↦ ?_) fun z hz y hy hzy ↦ ?_
    · -- Over `k`, the `C p` are independent because they lie in distinct pieces.
      refine linearIndependent_iUnion_finite (f := fun p (x : s p) ↦ (x : M)) hli
        fun p t _ hpt ↦ ?_
      simp only [Subtype.range_coe, hspan']
      refine (G.isInternal.submodule_iSupIndep p).mono (fun x hx ↦ (hCV p hx).1) ?_
      exact iSup₂_le fun q hq ↦ le_iSup₂_of_le q (fun h ↦ hpt (h ▸ hq))
        fun x hx ↦ (hCV q hx).1
    · -- `X` is a nonzerodivisor on `L`.
      exact (Submodule.disjoint_def.mp hLT) x (hspanL hx)
        ((Submodule.mem_torsion_iff x).mpr ⟨⟨X, X_mem_nonZeroDivisors⟩, hXx⟩)
    · -- Each component of `z` lies in both `C p` and `W p`.
      have hzero (p : ℤ) : (DirectSum.decompose G.piece z p : M) = 0 := by
        refine Submodule.disjoint_def.mp (hWC p) _ ?_ (hcomp hz p)
        rw [hzy, ← pow_one (X : k[X]), coe_decompose_X_pow_smul hX, Nat.cast_one, one_mul,
          pow_one]
        exact ⟨_, Submodule.mem_inf.mpr
          ⟨(DirectSum.decompose G.piece y (p + d)).2, hL _ (hspanL hy)⟩, rfl⟩
      rw [← DirectSum.sum_support_decompose G.piece z]
      exact Finset.sum_eq_zero fun p _ ↦ hzero p
  · -- Each homogeneous `x ∈ L` is `X • y + c` with `y` of higher degree and `c ∈ C p`.
    refine le_antisymm hspanL (le_of_forall_mem_piece_exists_sub_X_smul_mem hd
      (bddAbove_setOf_piece_ne_bot hX) hL fun p x hxG hxL ↦ ?_)
    have hx : x ∈ W p ⊔ C p := hWCV p ▸ Submodule.mem_inf.mpr ⟨hxG, hxL⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨hyG, hyL⟩ := Submodule.mem_inf.mp hy
    refine ⟨y, hyG, hyL, ?_⟩
    rw [← hspan' p] at hc
    have hcN : c ∈ Submodule.span k[X] (Set.range b) :=
      Submodule.span_le_restrictScalars k k[X] _
        (Submodule.span_mono (fun x hx ↦ (⟨⟨p, ⟨x, hx⟩⟩, rfl⟩ : x ∈ Set.range b)) hc)
    simpa using hcN

/-- **Graded freeness.** A finitely generated graded `k[X]`-module over a field that is torsion-free
over `k[X]`, and on which `X` lowers degree by `d ≠ 0`, has a `k[X]`-basis of homogeneous
elements. -/
theorem exists_homogeneous_basis [Module.IsTorsionFree k[X] M] (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    ∃ (ι : Type u) (b : Module.Basis ι k[X] M) (deg : ι → ℤ), ∀ i, b i ∈ G.piece (deg i) := by
  obtain ⟨ι, b, deg, hb, hli, hspan⟩ :=
    exists_linearIndependent_span_eq_of_disjoint_torsion hd hX ⊤ (fun _ _ _ ↦ Submodule.mem_top)
      (by simp [Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance])
  exact ⟨ι, Module.Basis.mk hli hspan.ge, deg, fun i ↦ by simpa using hb i⟩

/-- **The free part of the structure theorem.** In a finitely generated graded `k[X]`-module over
a field on which `X` lowers degree by `d ≠ 0`, the torsion submodule has a complement spanned by a
`k[X]`-linearly independent family of homogeneous elements: `M` is its torsion submodule plus a
graded free module, one `X`-tower for each element of the family. -/
theorem exists_linearIndependent_isCompl_torsion (hd : d ≠ 0)
    (hX : ∀ ⦃p : ℤ⦄ ⦃x : M⦄, x ∈ G.piece p → (X : k[X]) • x ∈ G.piece (p - d)) :
    ∃ (ι : Type u) (b : ι → M) (deg : ι → ℤ), (∀ i, b i ∈ G.piece (deg i)) ∧
      LinearIndependent k[X] b ∧
        IsCompl (Submodule.torsion k[X] M) (Submodule.span k[X] (Set.range b)) := by
  obtain ⟨L, hTL, hL⟩ := G.exists_isCompl_torsion_of_X_smul_mem_piece hd hX
  obtain ⟨ι, b, deg, hb, hli, hspan⟩ :=
    exists_linearIndependent_span_eq_of_disjoint_torsion hd hX L hL hTL.disjoint.symm
  exact ⟨ι, b, deg, hb, hli, hspan ▸ hTL⟩

-- The free tower `k[X]`, graded by minus the exponent, has a homogeneous basis.
example (k : Type) [Field k] : ∃ (ι : Type) (b : Module.Basis ι k[X] k[X]) (deg : ι → ℤ),
    ∀ i, b i ∈ (Polynomial.negDegreeGrading k).piece (deg i) :=
  (Polynomial.negDegreeGrading k).exists_homogeneous_basis one_ne_zero
    fun _ _ hx ↦ Polynomial.X_smul_mem_negDegreeGrading_piece hx

end TauCeti.InternalGrading
