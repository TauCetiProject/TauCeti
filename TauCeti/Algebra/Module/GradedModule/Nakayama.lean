/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
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

variable {k : Type uk} [CommSemiring k] {A : Type uA} [Semiring A] [Algebra k A]
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
      (decompose G.piece (a • y) p : M) ∈ S) ha (fun i a ha => ?_) ?_ ?_
    · refine Submodule.iSup_induction _ (motive := fun a =>
        (decompose G.piece (a • y) p : M) ∈ S) ha (fun hi a ha => ?_) ?_ ?_
      · let f : M →ₗ[k] M := Algebra.lsmul k k M a
        have hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece i :=
          TauCeti.LinearMap.isHomogeneous_def.mpr fun q z hz => by
            simpa [f, add_comm] using SetLike.GradedSMul.smul_mem ha hz
        have h := hf.map_decompose (p - i) y
        rw [sub_add_cancel] at h
        simpa only [f, Algebra.lsmul_apply] using h ▸ Submodule.subset_span
          ⟨i, hi, a, ha, _, (decompose G.piece y (p - i)).property, rfl⟩
      · simp
      · intro a b ha hb
        simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
          S.add_mem ha hb
    · simp
    · intro a b ha hb
      simpa only [add_smul, decompose_add, DirectSum.add_apply, Submodule.coe_add] using
        S.add_mem ha hb
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

/-- Any `A`-linear map sends `A₊ M` into `A₊ N`. -/
theorem map_mem_positive_smul_top {N : Type*} [AddCommMonoid N] [Module k N]
    [Module A N] [IsScalarTower k A N] (f : M →ₗ[A] N) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    f x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) :=
  Submodule.smul_induction_on hx
    (fun a ha _ _ => by
      rw [map_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top)
    (fun _ _ hx hy => by
      rw [map_add]
      exact add_mem hx hy)

section Endomorphism

variable {R : Type uk} [CommRing R] {B : Type uA} [Ring B] [Algebra R B]
  {N : Type uM} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]
  (ℬ : ℤ → Submodule R B) {H : InternalGrading R N ℤ} [SetLike.GradedSMul ℬ H.piece]

private theorem decompose_pow_eq_zero_of_forall_mem_positive_smul_top
    (b : ℤ) (hbelow : ∀ p < b, H.piece p = ⊥) (g : Module.End B N)
    (hg : ∀ y : N, g y ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule R N)) :
    ∀ (m : ℕ) (y : N) {p : ℤ}, p < b + m → (decompose H.piece ((g ^ m) y) p : N) = 0
  | 0, y, p, hp => by
      have hp' : p < b := by omega
      exact (Submodule.eq_bot_iff _).mp (hbelow p hp') _ (decompose H.piece y p).2
  | m + 1, y, p, hp => by
      rw [pow_succ, mul_apply_eq_comp]
      refine Submodule.smul_induction_on (hg y) (fun a ha z _ => ?_) (fun u v hu hv => ?_)
      · refine Submodule.iSup_induction _
          (motive := fun a => (decompose H.piece ((g ^ m) (a • z)) p : N) = 0)
          ha (fun i a ha => ?_) (by simp)
          (fun a₁ a₂ h₁ h₂ => by
            simp only [add_smul, map_add, decompose_add, DirectSum.add_apply, Submodule.coe_add,
              h₁, h₂, add_zero])
        refine Submodule.iSup_induction _
          (motive := fun a => (decompose H.piece ((g ^ m) (a • z)) p : N) = 0)
          ha (fun hi a ha => ?_) (by simp)
          (fun a₁ a₂ h₁ h₂ => by
            simp only [add_smul, map_add, decompose_add, DirectSum.add_apply, Submodule.coe_add,
              h₁, h₂, add_zero])
        rw [map_smul]
        let la : N →ₗ[R] N := Algebra.lsmul R R N a
        have hla : TauCeti.LinearMap.IsHomogeneous la H.piece H.piece i :=
          TauCeti.LinearMap.isHomogeneous_def.mpr fun q w hw => by
            simpa [la, add_comm] using SetLike.GradedSMul.smul_mem ha hw
        have hmap := hla.map_decompose (p - i) ((g ^ m) z)
        rw [sub_add_cancel] at hmap
        have hrec := decompose_pow_eq_zero_of_forall_mem_positive_smul_top b hbelow g hg m z
          (p := p - i) (by omega)
        exact Subtype.ext_iff.mp (by simpa [la, hrec] using hmap.symm) ▸ rfl
      · simp only [map_add, decompose_add, DirectSum.add_apply, Submodule.coe_add, hu, hv,
          add_zero]

/-- **Injectivity from Graded Nakayama.** On a bounded-below graded module, an `A`-linear
endomorphism congruent to the identity modulo `A₊ M` is injective. -/
theorem injective_of_sub_mem_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, H.piece p = ⊥)
    (f : N →ₗ[B] N)
    (hf : ∀ y : N, f y - y ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule R N)) :
    Function.Injective f := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  let g : Module.End B N := 1 - f
  have hg : ∀ y : N, g y ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule R N) := fun y => by
    have : g y = -(f y - y) := by simp [g]
    exact this ▸ neg_mem (hf y)
  have hgx : ∀ m : ℕ, (g ^ m) x = x := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => simp [pow_succ', ih, g, hx]
  rw [← sum_support_decompose H.piece x]
  refine Finset.sum_eq_zero fun p _ => ?_
  let m : ℕ := (p - b + 1).toNat
  rw [← hgx m]
  exact decompose_pow_eq_zero_of_forall_mem_positive_smul_top ℬ b hbelow g hg m x (by omega)

/-- **Surjectivity from Graded Nakayama.** On a bounded-below graded module, a degree-zero
homogeneous `A`-linear endomorphism congruent to the identity modulo `A₊ M` is surjective. -/
theorem surjective_of_sub_mem_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, H.piece p = ⊥)
    (f : N →ₗ[B] N) (hf_hom : TauCeti.LinearMap.IsHomogeneous f H.piece H.piece 0)
    (hf : ∀ y : N, f y - y ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule R N)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  refine eq_top_of_piece_le_sup_positive_smul_top ℬ (LinearMap.range f)
    (fun p y hy => ?_) b hbelow fun p x _ => ?_
  · obtain ⟨x, rfl⟩ := hy
    have hmap := hf_hom.map_decompose p x
    rw [add_zero] at hmap
    exact hmap ▸ ⟨_, rfl⟩
  · exact Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, -(f x - x), neg_mem (hf x), by abel⟩

/-- **Invertibility from Graded Nakayama.** On a bounded-below graded module, a degree-zero
homogeneous `A`-linear endomorphism congruent to the identity modulo `A₊ M` is bijective. -/
theorem bijective_of_sub_mem_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, H.piece p = ⊥)
    (f : N →ₗ[B] N) (hf_hom : TauCeti.LinearMap.IsHomogeneous f H.piece H.piece 0)
    (hf : ∀ y : N, f y - y ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule R N)) :
    Function.Bijective f :=
  ⟨injective_of_sub_mem_positive_smul_top ℬ b hbelow f hf,
    surjective_of_sub_mem_positive_smul_top ℬ b hbelow f hf_hom hf⟩

end Endomorphism

variable [GradedAlgebra 𝒜]

omit [IsScalarTower k A M] in
/-- Over a nonnegatively graded algebra, any finitely generated graded `A`-module is bounded
below in internal degree. -/
theorem exists_piece_eq_bot_of_lt [Module.Finite A M] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    ∃ b : ℤ, ∀ p < b, G.piece p = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let D : Finset ℤ := insert 0 (s.biUnion fun x => (decompose G.piece x).support)
  let b : ℤ := D.min' (Finset.insert_nonempty 0 _)
  have hgen : ∀ x ∈ (s : Set M), ∀ p < b, (decompose G.piece x p : M) = 0 := by
    intro x hx p hp
    have hpD : p ∉ D := fun hmem => not_le_of_gt hp (Finset.min'_le D p hmem)
    have hps : p ∉ (decompose G.piece x).support := fun hmem =>
      hpD (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, hx, hmem⟩))
    simpa [DFinsupp.mem_support_toFun] using hps
  have hall : ∀ m : M, ∀ p < b, (decompose G.piece m p : M) = 0 := by
    intro m
    have hm : m ∈ Submodule.span A (s : Set M) := hs.symm ▸ Submodule.mem_top
    refine Submodule.span_induction hgen (fun _ _ => by simp)
      (fun x y _ _ hx hy p hp => by simp [hx p hp, hy p hp]) (fun a x _ hx p hp => ?_) hm
    rw [← sum_support_decompose 𝒜 a, ← sum_support_decompose G.piece x, Finset.sum_smul]
    simp only [Finset.smul_sum, decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun q _ => ?_
    by_cases hi0 : i < 0
    · have ha0 : (decompose 𝒜 a i : A) = 0 :=
        (Submodule.eq_bot_iff _).mp (h𝒜 i hi0) _ (decompose 𝒜 a i).2
      simp [ha0]
    · by_cases hqb : q < b
      · simp [hx q hqb]
      · have hmem : (decompose 𝒜 a i : A) • (decompose G.piece x q : M) ∈ G.piece (i + q) := by
          simpa using SetLike.GradedSMul.smul_mem (decompose 𝒜 a i).2 (decompose G.piece x q).2
        exact decompose_of_mem_ne G.piece hmem (by omega)
  refine ⟨b, fun p hp => (Submodule.eq_bot_iff _).mpr fun x hx => ?_⟩
  simpa [decompose_of_mem_same G.piece hx] using hall x p hp

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

/-- The generating-degree criterion for a finitely generated graded `A`-module over a
nonnegatively graded algebra. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top_of_finite_module [Module.Finite A M]
    (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  obtain ⟨b, hb⟩ := G.exists_piece_eq_bot_of_lt 𝒜 h𝒜
  exact isGeneratedInDegree_iff_piece_le_positive_smul_top 𝒜 h𝒜 b hb d

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
