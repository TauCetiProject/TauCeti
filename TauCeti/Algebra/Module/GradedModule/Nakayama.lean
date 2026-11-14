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
is essential; no finite-generation hypothesis is required when a lower bound is supplied, while a
finitely generated module over a nonnegatively graded ring is bounded below automatically.

In the same bounded-below setting, any degree-zero module endomorphism congruent to the identity
modulo `A₊ M` is bijective: generation modulo `A₊` gives surjectivity, and the difference from the
identity raises internal degree on homogeneous components so its iterates kill any given degree.

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

/-- A finitely generated graded module over a nonnegatively decomposed scalar semiring vanishes
below some internal degree: its finite generating set has finitely many nonzero homogeneous
components, and nonnegative homogeneous scalars cannot lower internal degree. -/
theorem exists_piece_eq_bot_of_lt_of_moduleFinite [DirectSum.Decomposition 𝒜] [Module.Finite A M]
    (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) : ∃ b : ℤ, ∀ p < b, G.piece p = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let supp : Finset ℤ := s.biUnion fun g ↦ (decompose G.piece g).support
  obtain ⟨b, hb⟩ := supp.finite_toSet.bddBelow
  -- Elements whose homogeneous components vanish below `b` form an `A`-submodule containing `s`.
  let U : Submodule A M :=
    { carrier := {x : M | ∀ p < b, (decompose G.piece x p : M) = 0}
      zero_mem' := fun p _ ↦ by simp
      add_mem' := fun {x y} hx hy p hp ↦ by
        simp [decompose_add, hx p hp, hy p hp]
      smul_mem' := fun a {x} hx ↦ by
        induction a using DirectSum.Decomposition.inductionOn 𝒜 with
        | zero => intro p _; simp
        | add a₁ a₂ h₁ h₂ =>
          intro p hp
          simp [add_smul, decompose_add, h₁ p hp, h₂ p hp]
        | @homogeneous i a =>
          intro p hp
          rcases lt_or_ge i 0 with hi | hi
          · have ha0 : (a : A) = 0 := by
              simpa only [h𝒜 i hi, Submodule.mem_bot] using a.2
            simp [ha0]
          · let f : M →ₗ[k] M := Algebra.lsmul k k M (a : A)
            have hf : TauCeti.LinearMap.IsHomogeneous f G.piece G.piece i :=
              TauCeti.LinearMap.isHomogeneous_def.mpr fun q z hz ↦ by
                simpa [f, add_comm] using SetLike.GradedSMul.smul_mem a.2 hz
            have hmap := hf.map_decompose (p - i) x
            rw [sub_add_cancel] at hmap
            simpa only [f, Algebra.lsmul_apply, hx (p - i) (by omega), smul_zero] using hmap.symm }
  have hU : U = ⊤ := top_unique <| hs ▸ Submodule.span_le.mpr fun g hg p hp ↦ by
    by_contra hne
    have hmem : p ∈ supp := Finset.mem_biUnion.mpr
      ⟨g, hg, DFinsupp.mem_support_iff.mpr (Submodule.coe_eq_zero.not.mp hne)⟩
    exact hp.not_ge (hb hmem)
  refine ⟨b, fun p hp ↦ (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_⟩
  have hxU : x ∈ U := hU.symm ▸ Submodule.mem_top
  simpa only [decompose_of_mem_same G.piece hx] using hxU p hp

/-- The set of nonzero homogeneous pieces of a finitely generated module over a nonnegatively
decomposed scalar semiring is bounded below. -/
theorem bddBelow_setOf_piece_ne_bot_of_moduleFinite [DirectSum.Decomposition 𝒜]
    [Module.Finite A M] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    BddBelow {p : ℤ | G.piece p ≠ ⊥} := by
  obtain ⟨b, hb⟩ := exists_piece_eq_bot_of_lt_of_moduleFinite (G := G) 𝒜 h𝒜
  refine ⟨b, fun p hp ↦ ?_⟩
  by_contra hlt
  exact hp (hb p (lt_of_not_ge hlt))

section GradedAlgebra

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

/-- The generating-degree criterion for a finitely generated module over a nonnegatively graded
algebra: finite generation over `A` supplies boundedness below automatically. -/
theorem isGeneratedInDegree_iff_piece_le_positive_smul_top_of_moduleFinite [Module.Finite A M]
    (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) (d : ℤ) :
    G.IsGeneratedInDegree A d ↔
      ∀ p, p ≠ d → G.piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  obtain ⟨b, hb⟩ := exists_piece_eq_bot_of_lt_of_moduleFinite (G := G) 𝒜 h𝒜
  exact isGeneratedInDegree_iff_piece_le_positive_smul_top 𝒜 h𝒜 b hb d

end GradedAlgebra

section Endomorphism

variable {k' : Type uk} [CommRing k'] {A' : Type uA} [Ring A'] [Algebra k' A']
  {N : Type uM} [AddCommGroup N] [Module k' N] [Module A' N] [IsScalarTower k' A' N]
  (ℬ : ℤ → Submodule k' A') {H : InternalGrading k' N ℤ} [SetLike.GradedSMul ℬ H.piece]

/-- Iterates of a degree-zero `A`-linear endomorphism landing in `A₊ N` annihilate homogeneous
pieces of bounded degree: each application lowers the module degree needed to decompose into a
bounded-below support, so the `m`-th iterate vanishes below `b + m`. -/
theorem pow_apply_eq_zero_of_mem_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, H.piece p = ⊥)
    {δ : N →ₗ[A'] N} (hδhom : TauCeti.LinearMap.IsHomogeneous δ H.piece H.piece 0)
    (hδ : ∀ x, δ x ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule k' N))
    (m : ℕ) {p : ℤ} (hp : p < b + m) {x : N} (hx : x ∈ H.piece p) :
    (δ ^ m) x = 0 := by
  induction m generalizing p x with
  | zero =>
    rw [Nat.cast_zero, add_zero] at hp
    exact (Submodule.eq_bot_iff _).mp (hbelow p hp) x hx
  | succ m ih =>
    have hmem := decompose_mem_of_mem_positive_smul_top (G := H) ℬ
      (LinearMap.ker (δ ^ m)) (p := p)
      (fun q hq y hy ↦ LinearMap.mem_ker.mpr (ih (by omega) hy)) (hδ x)
    have hsame : (decompose H.piece (δ x) p : N) = δ x :=
      decompose_of_mem_same H.piece (by simpa only [add_zero] using hδhom.map_mem hx)
    rw [hsame, LinearMap.mem_ker] at hmem
    simpa only [pow_succ, mul_apply_eq_comp] using hmem

/-- **Graded Nakayama for degree-zero endomorphisms.** On a bounded-below graded module, any
degree-zero `A`-linear endomorphism congruent to the identity modulo `A₊ N` is bijective:
generation modulo `A₊` gives surjectivity, and iterating `id - f` shifts internal support below the
lower bound to give injectivity. Neither multiplicative algebra axioms nor finite generation are
needed once a lower bound is supplied. -/
theorem bijective_of_sub_id_mem_positive_smul_top (b : ℤ) (hbelow : ∀ p < b, H.piece p = ⊥)
    {f : N →ₗ[A'] N} (hf : TauCeti.LinearMap.IsHomogeneous f H.piece H.piece 0)
    (hsub : ∀ x, f x - x ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule k' N)) :
    Function.Bijective f := by
  let δ : N →ₗ[A'] N := LinearMap.id - f
  have hδ : ∀ x, δ x ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule k' N) := fun x ↦ by
    have hx : -(f x - x) ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule k' N) :=
      Submodule.neg_mem _ (hsub x)
    simpa only [δ, LinearMap.sub_apply, LinearMap.id_apply, neg_sub] using hx
  have hδhom : TauCeti.LinearMap.IsHomogeneous δ H.piece H.piece 0 :=
    TauCeti.LinearMap.isHomogeneous_def.mpr fun q y hy ↦ by
      simpa only [δ, LinearMap.sub_apply, LinearMap.id_apply, add_zero] using
        (H.piece q).sub_mem hy (by simpa only [add_zero] using hf.map_mem hy)
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    classical
    rw [← sum_support_decompose H.piece x]
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    set xp : N := ↑(decompose H.piece x p)
    have hfxp : f xp = 0 := by
      have hmap := hf.map_decompose p x
      simpa only [xp, hx, add_zero, decompose_zero, DirectSum.zero_apply,
        Submodule.coe_zero] using hmap
    have hδxp : δ xp = xp := by simp [δ, hfxp]
    have hfix : ∀ m : ℕ, (δ ^ m) xp = xp := fun m ↦ by
      induction m with
      | zero => simp
      | succ m ih => simp [pow_succ, hδxp, ih]
    let m : ℕ := (p - b + 1).toNat
    rw [← hfix m]
    exact pow_apply_eq_zero_of_mem_positive_smul_top (H := H) ℬ b hbelow hδhom hδ m (by omega)
      (decompose H.piece x p).2
  · rw [← LinearMap.range_eq_top]
    refine eq_top_of_piece_le_sup_positive_smul_top (G := H) ℬ (LinearMap.range f)
      hf.isHomogeneous_range b hbelow fun p x _ ↦ ?_
    have hdecomp : x = f x + δ x := by simp [δ]
    rw [hdecomp]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self f x) (hδ x)

/-- On a finitely generated graded module over a nonnegatively decomposed ring, any degree-zero
`A`-linear endomorphism congruent to the identity modulo `A₊ N` is bijective. -/
theorem bijective_of_sub_id_mem_positive_smul_top_of_moduleFinite [DirectSum.Decomposition ℬ]
    [Module.Finite A' N] (hℬ : ∀ i < 0, ℬ i = ⊥) {f : N →ₗ[A'] N}
    (hf : TauCeti.LinearMap.IsHomogeneous f H.piece H.piece 0)
    (hsub : ∀ x, f x - x ∈ (⨆ (i : ℤ) (_ : 0 < i), ℬ i) • (⊤ : Submodule k' N)) :
    Function.Bijective f := by
  obtain ⟨b, hb⟩ := exists_piece_eq_bot_of_lt_of_moduleFinite (G := H) ℬ hℬ
  exact bijective_of_sub_id_mem_positive_smul_top (H := H) ℬ b hb hf hsub

end Endomorphism

end TauCeti.InternalGrading
