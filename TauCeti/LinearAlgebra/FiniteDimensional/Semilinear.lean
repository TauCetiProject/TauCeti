/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.GroupTheory.GroupAction.Hom

/-!
# Injective and surjective semilinear endomorphisms of finite-dimensional spaces

An injective linear endomorphism of a finite-dimensional vector space is surjective, and vice versa
(`LinearMap.injective_iff_surjective`). The same holds for an endomorphism that is semilinear with
respect to a ring endomorphism `σ` of the scalars: `LinearMap.surjective_of_injectiveₛₗ` (when
`σ` is surjective) and `LinearMap.injective_of_surjectiveₛₗ` (for any `σ : K →+* K`). Moreover,
the descending chain of iterated images `(Submodule.map f)^[n] ⊤` stabilizes by step
`Module.finrank K V` (`LinearMap.iterate_map_top_finrank_add_one`,
`LinearMap.map_iterate_map_top_finrank`), so `f` restricts to a bijection on
`(Submodule.map f)^[Module.finrank K V] ⊤` (`LinearMap.bijective_restrict_iterate_map_top`).
Also, any ring endomorphism admitting a surjective semilinear endomorphism on a nontrivial
finite-dimensional space is itself surjective (`LinearMap.ringHomSurjective_of_surjectiveₛₗ`).
We also record that the representation matrix of a surjective semilinear endomorphism in a finite
basis has unit determinant (`LinearMap.isUnit_det_basis_matrix_of_surjectiveₛₗ`), and that
solvability of scalar difference polynomials transfers to surjectivity of `Φ - 1`
(`LinearMap.surjective_sub_id_of_surjective_sum_mul_iterate`).
-/

public section

namespace LinearMap

/-- Evaluating a `σ`-semilinear map at `u` expands in a finite basis `b` as
`∑ i, σ (b.repr u i) • f (b i)`. -/
theorem map_eq_sum_repr_smulₛₗ {ι K K' V W : Type*} [Semiring K] [Semiring K']
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K' W] [Fintype ι]
    {σ : K →+* K'} (b : Module.Basis ι K V) (f : V →ₛₗ[σ] W) (u : V) :
    f u = ∑ i, σ (b.repr u i) • f (b i) := by
  conv_lhs => rw [← b.sum_repr u, map_sum]
  simp [map_smulₛₗ]

section SurjectiveInjective

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K}

/-- On a nontrivial finite-dimensional vector space over a division ring, any ring endomorphism `σ`
admitting a surjective `σ`-semilinear endomorphism `f` is itself surjective. -/
theorem ringHomSurjective_of_surjectiveₛₗ [Nontrivial V] {f : V →ₛₗ[σ] V}
    (hf : Function.Surjective f) : RingHomSurjective σ := by
  refine ⟨fun c ↦ ?_⟩; by_contra hc
  -- Pick preimages of `b i` and `c • b i` under `f`, and record their `σ`-semilinear expansions.
  let b := Module.finBasis K V; set d := Module.finrank K V
  have hd : 0 < d := Module.finrank_pos
  have hspan (v : V) : ∃ a : Fin d → K, ∑ j, σ (a j) • f (b j) = v := by
    obtain ⟨u, rfl⟩ := hf v
    exact ⟨b.repr u, (map_eq_sum_repr_smulₛₗ b f u).symm⟩
  choose A hA using fun i : Fin d ↦ hspan (b i)
  choose B hB using fun i : Fin d ↦ hspan (c • b i)
  -- The `2 * d` coefficient rows in `K^d` are linearly dependent over `K`.
  let u : Fin d × Bool → (Fin d → K) := fun p ↦ if p.2 then B p.1 else A p.1
  have hnot : ¬ LinearIndependent K u := fun hli ↦ by
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Module.finrank_pi,
      Fintype.card_fin] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hnot
  obtain ⟨g, hg0, ⟨p₀, hp₀⟩⟩ := hnot
  -- Push that linear dependence through `σ` to obtain a vanishing combination of `b i`.
  have hsum_j (j : Fin d) :
      ∑ i, (σ (g (i, false)) * σ (A i j) + σ (g (i, true)) * σ (B i j)) = 0 := by
    have hgj := congrFun hg0 j
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, u, Bool.false_eq_true, ↓reduceIte,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgj
    simpa only [map_sum, map_add, map_mul, map_zero, add_comm] using congrArg σ hgj
  have hcomb : ∑ i : Fin d, (σ (g (i, false)) + σ (g (i, true)) * c) • b i = 0 := by
    calc ∑ i : Fin d, (σ (g (i, false)) + σ (g (i, true)) * c) • b i
        = ∑ i : Fin d, (σ (g (i, false)) • ∑ j, σ (A i j) • f (b j) +
            σ (g (i, true)) • ∑ j, σ (B i j) • f (b j)) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_; rw [hA i, hB i, add_smul, smul_smul]
      _ = ∑ j : Fin d, (∑ i : Fin d,
            (σ (g (i, false)) * σ (A i j) + σ (g (i, true)) * σ (B i j))) • f (b j) := by
          simp only [Finset.smul_sum, smul_smul, Finset.sum_smul, add_smul, Finset.sum_add_distrib]
          rw [Finset.sum_comm]
          conv_lhs => arg 2; rw [Finset.sum_comm]
      _ = 0 := by simp [hsum_j]
  -- At a nonzero coordinate `p₀`, linear independence of `b` yields a `σ`-preimage of `c`.
  rcases p₀ with ⟨i₀, b₀⟩
  have hcoeff := Fintype.linearIndependent_iff.1 b.linearIndependent _ hcomb i₀
  by_cases hy : g (i₀, true) = 0
  · have hx : g (i₀, false) ≠ 0 := by cases b₀ <;> simp_all
    rw [hy, map_zero, zero_mul, add_zero] at hcoeff
    exact hx (σ.injective (hcoeff.trans (map_zero σ).symm))
  · refine hc ⟨-(g (i₀, true))⁻¹ * g (i₀, false), ?_⟩
    have hσy : σ (g (i₀, true)) ≠ 0 := fun h ↦ hy (σ.injective (h.trans (map_zero σ).symm))
    have h1 := eq_neg_of_add_eq_zero_left hcoeff
    rw [map_mul, map_neg, map_inv₀, neg_mul, h1, mul_neg, neg_neg, inv_mul_cancel_left₀ hσy]

/-- A surjective endomorphism of a finite-dimensional vector space that is semilinear with
respect to a ring endomorphism of the scalars is injective. -/
theorem injective_of_surjectiveₛₗ {f : V →ₛₗ[σ] V} (hf : Function.Surjective f) :
    Function.Injective f := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Function.injective_of_subsingleton f
  have hσ : Function.Bijective σ :=
    ⟨σ.injective, (ringHomSurjective_of_surjectiveₛₗ hf).is_surjective⟩
  let g : (V ⧸ ker f) →ₛₗ[σ] V := (ker f).liftQ f le_rfl
  have hginj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun x hx => by
    induction x using Submodule.Quotient.induction_on with
    | H x => exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have hgsurj : Function.Surjective g := fun y =>
    let ⟨x, hx⟩ := hf y
    ⟨Submodule.Quotient.mk x, hx⟩
  have hrank : Module.rank K (V ⧸ ker f) = Module.rank K V :=
    rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective g.toAddMonoidHom ⟨hginj, hgsurj⟩) hσ
      (map_smulₛₗ g)
  have hfin : Module.finrank K (V ⧸ ker f) = Module.finrank K V := congrArg Cardinal.toNat hrank
  have hker : Module.finrank K (ker f) = 0 := by
    have := Submodule.finrank_quotient_add_finrank (ker f)
    omega
  exact (injective_iff_map_eq_zero f).2 fun x hx => by
    have hbot : ker f = ⊥ := Submodule.finrank_eq_zero.1 hker
    rw [← mem_ker, hbot, Submodule.mem_bot] at hx
    exact hx

/-- An injective endomorphism of a finite-dimensional vector space that is semilinear with
respect to a surjective ring endomorphism of the scalars is surjective. -/
theorem surjective_of_injectiveₛₗ [RingHomSurjective σ] {f : V →ₛₗ[σ] V}
    (hf : Function.Injective f) : Function.Surjective f := by
  have hσ : Function.Bijective σ := ⟨σ.injective, RingHomSurjective.is_surjective⟩
  have hrank : Module.rank K V = Module.rank K (range f) :=
    rank_eq_of_equiv_equiv σ
      (AddEquiv.ofBijective f.rangeRestrict.toAddMonoidHom
        ⟨fun x y h => hf (congrArg Subtype.val h), f.surjective_rangeRestrict⟩)
      hσ fun r x => Subtype.ext (map_smulₛₗ f r x)
  rw [← range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (congrArg Cardinal.toNat hrank).symm

/-- On a finite-dimensional vector space, an endomorphism semilinear with respect to a surjective
ring endomorphism of the scalars is injective if and only if it is surjective. -/
theorem injective_iff_surjectiveₛₗ [RingHomSurjective σ] {f : V →ₛₗ[σ] V} :
    Function.Injective f ↔ Function.Surjective f :=
  ⟨surjective_of_injectiveₛₗ, injective_of_surjectiveₛₗ⟩

end SurjectiveInjective

section BasisMatrix

/-- If `f : V →ₛₗ[σ] V` is a surjective `σ`-semilinear endomorphism of a free module with finite
basis `b : Basis ι K V`, then the matrix `(b.repr (f (b i)) k)` has unit determinant. -/
theorem isUnit_det_basis_matrix_of_surjectiveₛₗ {ι K V : Type*} [CommRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] {σ : K →+* K}
    (b : Module.Basis ι K V) {f : V →ₛₗ[σ] V} (hf : Function.Surjective f) :
    IsUnit (Matrix.of fun i k ↦ b.repr (f (b i)) k).det := by
  let B : Matrix ι ι K := Matrix.of fun i k ↦ b.repr (f (b i)) k
  choose u hu using fun j : ι ↦ hf (b j)
  let A : Matrix ι ι K := Matrix.of fun j i ↦ σ (b.repr (u j) i)
  have hAB : A * B = 1 := by
    ext j k
    have hrep := congrArg (fun x ↦ b.repr x k) (hu j)
    rw [map_eq_sum_repr_smulₛₗ b f (u j), map_sum] at hrep
    simp only [map_smul, Module.Basis.repr_self, Finsupp.single_apply] at hrep
    simpa [A, B, Matrix.mul_apply, Matrix.one_apply, eq_comm] using hrep.symm
  exact isUnit_iff_exists_inv'.2 ⟨A.det, by rw [← Matrix.det_mul, hAB, Matrix.det_one]⟩

end BasisMatrix

section IterateImage

variable {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V] {σ : K →+* K}
  [RingHomSurjective σ]

/-- Membership in the `n`-th iterated image of `⊤` under a semilinear endomorphism. -/
theorem mem_iterate_map_top_iff (f : V →ₛₗ[σ] V) (n : ℕ) (x : V) :
    x ∈ (Submodule.map f)^[n] ⊤ ↔ x ∈ Set.range (f^[n]) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ', Submodule.mem_map]
    refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun ⟨y, hy⟩ => ?_⟩
    · obtain ⟨z, rfl⟩ := (ih y).1 hy
      exact ⟨z, hyx⟩
    · exact ⟨f^[n] y, (ih _).2 ⟨y, rfl⟩, hy⟩

/-- The sequence of iterated images `(Submodule.map f)^[n] ⊤` is antitone. -/
theorem iterate_map_top_antitone (f : V →ₛₗ[σ] V) :
    Antitone fun n => (Submodule.map f)^[n] (⊤ : Submodule K V) :=
  antitone_nat_of_succ_le fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      conv_lhs => rw [Function.iterate_succ_apply']
      conv_rhs => rw [Function.iterate_succ_apply']
      exact Submodule.map_mono ih

/-- The iterated image `(Submodule.map f)^[Module.finrank K V] ⊤` is nonzero when some
vector has nonzero `Module.finrank K V`-th iterate. -/
theorem iterate_map_top_ne_bot_of_iterate_ne_zero (f : V →ₛₗ[σ] V) {v : V}
    (hf : f^[Module.finrank K V] v ≠ 0) :
    (Submodule.map f)^[Module.finrank K V] (⊤ : Submodule K V) ≠ ⊥ := by
  intro hbot
  apply hf
  have hx : f^[Module.finrank K V] v ∈
      (Submodule.map f)^[Module.finrank K V] (⊤ : Submodule K V) :=
    (mem_iterate_map_top_iff f _ _).2 ⟨v, rfl⟩
  rw [hbot, Submodule.mem_bot] at hx
  exact hx

end IterateImage

/-- The descending chain of iterated images of a semilinear endomorphism stabilizes by step
`Module.finrank K V`. -/
theorem iterate_map_top_finrank_add_one {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {σ : K →+* K} [RingHomSurjective σ]
    (f : V →ₛₗ[σ] V) :
    (Submodule.map f)^[Module.finrank K V + 1] (⊤ : Submodule K V) =
      (Submodule.map f)^[Module.finrank K V] ⊤ := by
  suffices h : ∃ n ≤ Module.finrank K V,
      (Submodule.map f)^[n + 1] (⊤ : Submodule K V) = (Submodule.map f)^[n] ⊤ by
    obtain ⟨n, hn, hRn⟩ := h
    have hconst : ∀ k,
        (Submodule.map f)^[n + k] (⊤ : Submodule K V) = (Submodule.map f)^[n] ⊤ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← Nat.add_assoc, Function.iterate_succ_apply', ih,
          ← Function.iterate_succ_apply' (Submodule.map f) n ⊤, hRn]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    rw [hk, Nat.add_assoc, hconst, hconst]
  by_contra! hne
  have hdec : ∀ n ≤ Module.finrank K V + 1,
      Module.finrank K ((Submodule.map f)^[n] (⊤ : Submodule K V)) + n ≤
        Module.finrank K V := by
    intro n hn
    induction n with
    | zero =>
      rw [Function.iterate_zero_apply, add_zero]
      exact Submodule.finrank_le ⊤
    | succ n ih =>
      have hlt : (Submodule.map f)^[n + 1] (⊤ : Submodule K V) < (Submodule.map f)^[n] ⊤ :=
        lt_of_le_of_ne ((iterate_map_top_antitone f) (Nat.le_succ n)) (hne n (by omega))
      have := Submodule.finrank_lt_finrank_of_lt hlt
      have := ih (by omega)
      omega
  have := hdec (Module.finrank K V + 1) le_rfl
  omega

/-- Applying a semilinear endomorphism `f` to its stabilized iterated image
`(Submodule.map f)^[Module.finrank K V] ⊤` maps that submodule onto itself. -/
theorem map_iterate_map_top_finrank {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {σ : K →+* K} [RingHomSurjective σ]
    (f : V →ₛₗ[σ] V) :
    Submodule.map f ((Submodule.map f)^[Module.finrank K V] (⊤ : Submodule K V)) =
      (Submodule.map f)^[Module.finrank K V] ⊤ := by
  rw [← Function.iterate_succ_apply' (Submodule.map f) (Module.finrank K V) ⊤]
  exact iterate_map_top_finrank_add_one f

/-- Restricting a semilinear endomorphism `f` to its stabilized iterated image
`(Submodule.map f)^[Module.finrank K V] ⊤` gives a bijective endomorphism. -/
theorem bijective_restrict_iterate_map_top {K V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {σ : K →+* K} [RingHomSurjective σ]
    (f : V →ₛₗ[σ] V) :
    Function.Bijective
      (f.restrict (p := (Submodule.map f)^[Module.finrank K V] ⊤)
        (q := (Submodule.map f)^[Module.finrank K V] ⊤)
        fun _ hx ↦ (map_iterate_map_top_finrank f).le (Submodule.mem_map_of_mem hx)) := by
  have hsurj : Function.Surjective
      (f.restrict (p := (Submodule.map f)^[Module.finrank K V] ⊤)
        (q := (Submodule.map f)^[Module.finrank K V] ⊤)
        fun _ hx ↦ (map_iterate_map_top_finrank f).le (Submodule.mem_map_of_mem hx)) := by
    rintro ⟨y, hy⟩
    rw [← map_iterate_map_top_finrank f, Submodule.mem_map] at hy
    obtain ⟨x, hx, hfx⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  exact ⟨injective_of_surjectiveₛₗ hsurj, hsurj⟩

section

open Finset Function

/-- If every scalar difference polynomial in `σ` with at least one nonzero coefficient acts
surjectively, then `Φ - 1` is surjective for each finite-dimensional `σ`-semilinear endomorphism. -/
theorem surjective_sub_id_of_surjective_sum_mul_iterate {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (σ : K ≃+* K)
    (hσ : ∀ (s : Finset ℕ) (a : ℕ → K), (∃ i ∈ s, a i ≠ 0) →
      Surjective (fun x : K => ∑ i ∈ s, a i * σ^[i] x))
    (Φ : V →ₛₗ[(σ : K →+* K)] V) : Surjective (fun x => Φ x - x) := by
  classical
  intro v
  -- The first `finrank + 1` iterates of the target vector satisfy a nonzero relation.
  let n := Module.finrank K V
  let u (i : Fin (n + 1)) := Φ^[n - i.val] v
  have hu : ¬ LinearIndependent K u := by
    intro h
    simpa [n] using h.fintype_card_le_finrank
  obtain ⟨a, ha, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hu
  -- Untwist each relation coefficient by the corresponding Frobenius power.
  let c (i : Fin (n + 1)) := σ.symm^[n - i.val] (a i)
  have hinverse : LeftInverse σ σ.symm := σ.apply_symm_apply
  have hinv (i : Fin (n + 1)) : σ^[n - i.val] (c i) = a i := hinverse.iterate _ _
  let d := Function.extend Fin.val c 0
  have hd : ∃ i ∈ Finset.range (n + 1), d i ≠ 0 := by
    refine ⟨i₀, Finset.mem_range.mpr i₀.isLt, ?_⟩
    simp only [d, Fin.val_injective.extend_apply]
    intro hi
    apply hi₀
    rw [← hinv i₀, hi]
    exact iterate_fixed (map_zero σ) _
  obtain ⟨z, hz⟩ := hσ _ d hd (-1)
  let w (i : Fin (n + 1)) := (c i * σ^[i.val] z) • v
  have hsum : ∑ i, w i = -v := by
    have hz' : (∑ i : Fin (n + 1), c i * σ^[i.val] z) = -1 := by
      simpa only [← Fin.sum_univ_eq_sum_range, d, Fin.val_injective.extend_apply] using hz
    simp only [w, ← sum_smul, hz', neg_one_smul]
  have hiter (i : Fin (n + 1)) :
      Φ^[n - i.val] (w i) = σ^[n] z • (a i • u i) := by
    have hindex : n - i.val + i.val = n := Nat.sub_add_cancel (by omega)
    have hscalar : σ^[n - i.val] (c i * σ^[i.val] z) = σ^[n] z * a i := by
      rw [iterate_map_mul, hinv, ← iterate_add_apply, hindex, mul_comm]
    simp only [w, u, TauCeti.iterate_map_smulₛₗ Φ, RingEquiv.coe_toRingHom, hscalar, smul_smul]
  -- The iterated terms sum to zero, and their starting terms sum to `-v`.
  refine ⟨∑ i : Fin (n + 1), ∑ j ∈ Finset.range (n - i.val), Φ^[j] (w i), ?_⟩
  dsimp only
  rw [map_sum, ← sum_sub_distrib]
  simp_rw [TauCeti.map_sum_iterate_sub, hiter]
  rw [sum_sub_distrib, ← smul_sum]
  simp [ha, hsum]

end

end LinearMap
