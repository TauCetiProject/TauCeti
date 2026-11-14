/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Generated
import TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Graded Nakayama and detection of generating degrees

For a bounded-below internally graded module, the positive-degree part of the algebra cannot
surject onto the whole module unless the module is zero. More generally, homogeneous generators
modulo the positive-degree action generate the module itself, and any degree-zero homogeneous
endomorphism congruent to the identity modulo `A₊ M` is bijective. Over a nonnegatively decomposed
algebra, every finitely generated graded `A`-module is automatically bounded below, and a
bounded-below module over a nonnegatively graded algebra is generated in degree `d` exactly when
every homogeneous piece outside degree `d` lies in `A₊ M`.

The generation criterion expresses concentration of `M / A₊ M` in degree `d` without choosing a
presentation of that quotient. It detects the generating degrees of terms of minimal graded
projective resolutions, while endomorphism bijectivity makes minimal resolutions unique up to
graded isomorphism. Neither projectivity nor semisimplicity is needed. Boundedness below is
essential; no finite-generation hypothesis is required when a lower bound is supplied.

The positive-degree action `A₊ M` is itself a homogeneous submodule, stable under degree-zero
scalars: its degree-`p` components are sums of products `a • y` with `a` of positive degree `i`
and `y` of degree `p - i`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of graded rings*, Section 2.3, for graded modules.
* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for detection of linearity via the generating degrees of minimal resolutions.
-/

public section

namespace TauCeti.InternalGrading

open _root_.DirectSum

universe uk uA uM

section BoundedBelow

variable {k : Type uk} [Semiring k] {A : Type uA} [Semiring A] [Module k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M]
  (𝒜 : ℤ → Submodule k A) [DirectSum.Decomposition 𝒜]
  {G : InternalGrading k M ℤ} [SetLike.GradedSMul 𝒜 G.piece]

/-- A finitely generated graded `A`-module over a nonnegatively decomposed algebra has no nonzero
homogeneous elements below some degree. -/
theorem bddBelow_setOf_piece_ne_bot [Module.Finite A M] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    BddBelow {p | G.piece p ≠ ⊥} := by
  -- Every element is an `A`-linear combination of the finitely many homogeneous components of a
  -- finite generating set, and scalar multiplication by `A` never lowers degree.
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  obtain ⟨b, hb⟩ : BddBelow (⋃ g ∈ s, ((decompose G.piece g).support : Set ℤ)) :=
    (s.finite_toSet.biUnion fun g _ ↦ Finset.finite_toSet _).bddBelow
  let L : Submodule k M := ⨆ q : Set.Ici b, G.piece q
  have hAL (a : A) : ∀ y ∈ L, a • y ∈ L := by
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add a₁ a₂ ha₁ ha₂ =>
      exact fun y hy ↦ by simpa only [add_smul] using L.add_mem (ha₁ y hy) (ha₂ y hy)
    | @homogeneous i a =>
      obtain ⟨a, ha⟩ := a
      intro y hy
      rcases lt_or_ge i 0 with hi | hi
      · rw [h𝒜 i hi, Submodule.mem_bot] at ha
        simp [ha]
      · refine Submodule.iSup_induction _ (motive := fun y ↦ a • y ∈ L) hy (fun q y hyq ↦ ?_)
          (by simp) fun y₁ y₂ hy₁ hy₂ ↦ by simpa only [smul_add] using L.add_mem hy₁ hy₂
        have hbq : b ≤ i + (q : ℤ) := by
          have hqb : b ≤ (q : ℤ) := q.2
          omega
        exact Submodule.mem_iSup_of_mem ⟨i + (q : ℤ), hbq⟩ (SetLike.GradedSMul.smul_mem ha hyq)
  let L' : Submodule A M := { L.toAddSubmonoid with smul_mem' := hAL }
  have hL (y : M) : y ∈ L := by
    have hsL : Submodule.span A (s : Set M) ≤ L' := Submodule.span_le.mpr fun g hg ↦ by
      rw [← sum_support_decompose G.piece g]
      exact L.sum_mem fun q hq ↦ Submodule.mem_iSup_of_mem
        ⟨q, hb (Set.mem_biUnion hg hq)⟩ (decompose G.piece g q).2
    exact hsL (hs ▸ Submodule.mem_top)
  refine ⟨b, fun p hp ↦ ?_⟩
  by_contra! hpb
  refine hp (eq_bot_iff.mpr fun x hx ↦ ?_)
  refine Submodule.disjoint_def.mp (G.isInternal.submodule_iSupIndep p) x hx ?_
  refine (iSup_le fun q ↦ ?_ : L ≤ ⨆ j, ⨆ (_ : j ≠ p), G.piece j) (hL x)
  exact le_iSup₂_of_le (q : ℤ) (hpb.trans_le q.2).ne' le_rfl

end BoundedBelow

section PositiveSMul

variable {k : Type uk} [Semiring k] {A : Type uA} [Semiring A] [Module k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝒜 : ℤ → Submodule k A) {G : InternalGrading k M ℤ} [SetLike.GradedSMul 𝒜 G.piece]

/-- The degree-`p` component of an element of `A₊ M` is a sum of products `a • y` with `a` of
some positive degree `i` and `y` of degree `p - i`. -/
theorem decompose_mem_span_of_mem_positive_smul_top {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) (p : ℤ) :
    (decompose G.piece x p : M) ∈ Submodule.span k
      {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z} := by
  classical
  set S := Submodule.span k {z | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ G.piece (p - i), a • y = z}
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · refine Submodule.iSup_induction _ (motive := fun a =>
      (decompose G.piece (a • y) p : M) ∈ S) ha (fun i a ha => ?_) (by simp) fun a b ha hb => by
        simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          S.add_mem ha hb
    refine Submodule.iSup_induction _ (motive := fun a =>
      (decompose G.piece (a • y) p : M) ∈ S) ha (fun hi a ha => ?_) (by simp) fun a b ha hb => by
        simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          S.add_mem ha hb
    have hy_eq : (decompose G.piece (a • y) p : M) =
        ∑ q ∈ (decompose G.piece y).support,
          (decompose G.piece (a • (decompose G.piece y q : M)) p : M) := by
      conv_lhs => rw [← sum_support_decompose G.piece y]
      rw [Finset.smul_sum, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    rw [hy_eq]
    refine S.sum_mem fun q _ => ?_
    by_cases hqp : i + q = p
    · rw [decompose_of_mem_same G.piece
        (hqp ▸ SetLike.GradedSMul.smul_mem ha (decompose G.piece y q).property)]
      exact Submodule.subset_span
        ⟨i, hi, a, ha, _, (by omega : q = p - i) ▸ (decompose G.piece y q).property, rfl⟩
    · rw [decompose_of_mem_ne G.piece
        (SetLike.GradedSMul.smul_mem ha (decompose G.piece y q).property) hqp]
      exact S.zero_mem
  · simpa only [decompose_add, DirectSum.add_apply, Submodule.coe_add] using S.add_mem hx hy

/-- A component of `A₊ M` lies in an `A`-submodule if all lower-degree pieces do. The positive
scalar lowers the degree of the module component needed to compute that component. -/
theorem decompose_mem_of_mem_positive_smul_top (U : Submodule A M) {p : ℤ}
    (hU : ∀ q < p, ∀ x ∈ G.piece q, x ∈ U) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    (decompose G.piece x p : M) ∈ U := by
  refine (Submodule.span_le (p := U.restrictScalars k)).mpr ?_
    (decompose_mem_span_of_mem_positive_smul_top 𝒜 hx p)
  rintro _ ⟨i, hi, a, -, y, hy, rfl⟩
  exact U.smul_mem a (hU (p - i) (by omega) y hy)

end PositiveSMul

section Endomorphism

variable {k : Type uk} [Semiring k] {A : Type uA} [Semiring A] [Module k A]
  {M : Type uM} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝒜 : ℤ → Submodule k A) {G : InternalGrading k M ℤ} [SetLike.GradedSMul 𝒜 G.piece]

/-- **Graded Nakayama for endomorphisms.** On a bounded-below graded `A`-module, every degree-zero
homogeneous `A`-linear endomorphism congruent to the identity modulo `A₊ M` is bijective. -/
theorem bijective_of_sub_mem_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥)
    {f : M →ₗ[A] M} (hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece 0)
    (hsub : ∀ x, f x - x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    Function.Bijective f := by
  -- `f - 1` strictly lowers the increasing `A`-submodule filtration generated by homogeneous
  -- pieces below `b + n`, so it is locally nilpotent.
  have hneg {q : ℤ} {y : M} (hy : y ∈ G.piece q) : -y ∈ G.piece q := by
    classical
    rw [← sum_support_decompose G.piece (-y)]
    refine (G.piece q).sum_mem fun r _ ↦ ?_
    by_cases hqr : q = r
    · exact hqr ▸ (decompose G.piece (-y) r).property
    · have h0 := congr_arg (fun z ↦ (decompose G.piece z r : M)) (add_neg_cancel y)
      simp only [decompose_add, DirectSum.add_apply, Submodule.coe_add, decompose_zero,
        DirectSum.zero_apply, ZeroMemClass.coe_zero] at h0
      rw [decompose_of_mem_ne G.piece hy hqr, zero_add] at h0
      simp [h0]
  let filt : ℕ → Submodule A M := fun n ↦
    Submodule.span A (⋃ (q : ℤ) (_ : q < b + n), (G.piece q : Set M))
  have hfilt0 : filt 0 = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro x ⟨_, ⟨q, rfl⟩, _, ⟨hq, rfl⟩, hx⟩
    simpa [hbelow q (by omega)] using hx
  have hfilt_exh (x : M) : ∃ n, x ∈ filt n := by
    classical
    obtain ⟨B, hB⟩ := (Finset.finite_toSet (decompose G.piece x).support).bddAbove
    refine ⟨(B - b + 1).toNat, ?_⟩
    rw [← sum_support_decompose G.piece x]
    refine (filt _).sum_mem fun q hq ↦ Submodule.subset_span ?_
    exact Set.mem_iUnion₂.mpr ⟨q, by have := hB hq; omega, (decompose G.piece x q).property⟩
  refine Module.End.bijective_of_sub_mem_filtration hfilt0 hfilt_exh fun n x hx ↦ ?_
  let g : M →ₗ[A] M := f - LinearMap.id
  have hgx_eq (y : M) : f y - y = g y := rfl
  rw [hgx_eq, ← Submodule.mem_comap]
  refine Submodule.span_le.mpr ?_ hx
  rintro x ⟨_, ⟨q, rfl⟩, _, ⟨hq, rfl⟩, hxq⟩
  have hgx : g x ∈ G.piece q := by
    rw [← hgx_eq, sub_eq_add_neg]
    exact (G.piece q).add_mem (by simpa [add_zero] using hf.map_mem hxq) (hneg hxq)
  rw [SetLike.mem_coe, Submodule.mem_comap, ← decompose_of_mem_same G.piece hgx, ← hgx_eq]
  exact decompose_mem_of_mem_positive_smul_top 𝒜 (filt n)
    (fun r hr y hy ↦ Submodule.subset_span <| Set.mem_iUnion₂.mpr ⟨r, by omega, hy⟩) (hsub x)

end Endomorphism

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
  {M : Type uM} [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝒜 : ℤ → Submodule k A) {G : InternalGrading k M ℤ} [SetLike.GradedSMul 𝒜 G.piece]

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
    | ind n ih =>
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

/-- **Graded Nakayama below a degree.** In a bounded-below graded module, if every homogeneous
piece below degree `e` lies in `A₊ M`, then all those pieces vanish. -/
theorem piece_eq_bot_of_piece_le_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, G.piece p = ⊥)
    {e : ℤ} (h : ∀ p < e, G.piece p ≤ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M))
    {p : ℤ} (hp : p < e) : G.piece p = ⊥ := by
  induction hn : (p - b).toNat using Nat.strong_induction_on generalizing p with
  | ind n ih =>
    by_cases hpb : p < b
    · exact hbelow p hpb
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have hU := decompose_mem_of_mem_positive_smul_top 𝒜 (⊥ : Submodule A M) (p := p)
      (fun q hq y hy ↦ by
        have hq' : G.piece q = ⊥ := if hqb : q < b then hbelow q hqb else
          ih (q - b).toNat (by omega) (hq.trans hp) rfl
        rw [hq'] at hy
        simpa using hy) (h p hp hx)
    rwa [decompose_of_mem_same G.piece hx, Submodule.mem_bot] at hU

/-- The positive-degree action `A₊ M` is a homogeneous submodule. -/
theorem isHomogeneous_positive_smul_top :
    SetLike.IsHomogeneous G.piece ((⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) := by
  intro p x hx
  refine Submodule.span_le.mpr ?_ (decompose_mem_span_of_mem_positive_smul_top 𝒜 hx p)
  rintro _ ⟨i, hi, a, ha, y, -, rfl⟩
  exact Submodule.smul_mem_smul (Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi ha))
    Submodule.mem_top

variable {𝒜} in
/-- Degree-zero scalars preserve the positive-degree action `A₊ M`. -/
theorem smul_mem_positive_smul_top [SetLike.GradedMul 𝒜] {a : A} (ha : a ∈ 𝒜 0) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    a • x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  have hmul : ∀ b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i, a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
    intro b hb
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun i b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    refine Submodule.iSup_induction _ (motive := fun b => a * b ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i)
      hb (fun hi b hb => ?_) (by simp) (fun b c hb hc => by simpa [mul_add] using add_mem hb hc)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hi
      (by simpa using SetLike.GradedMul.mul_mem ha hb))
  refine Submodule.smul_induction_on hx (fun b hb y _ => ?_) (fun x y hx hy => ?_)
  · rw [← mul_smul]
    exact Submodule.smul_mem_smul (hmul b hb) Submodule.mem_top
  · simpa only [smul_add] using Submodule.add_mem _ hx hy

omit G [SetLike.GradedSMul 𝒜 G.piece] in
variable {𝒜} in
/-- Every `A`-linear map sends `A₊ M` into `A₊ N`. -/
theorem map_mem_positive_smul_top {N : Type*} [AddCommMonoid N] [Module k N] [Module A N]
    [IsScalarTower k A N] (f : M →ₗ[A] N) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    f x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) :=
  Submodule.smul_induction_on hx
    (fun a ha y _ ↦ by simpa only [map_smul] using Submodule.smul_mem_smul ha Submodule.mem_top)
    fun x₁ x₂ hx₁ hx₂ ↦ by simpa only [map_add] using add_mem hx₁ hx₂

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
