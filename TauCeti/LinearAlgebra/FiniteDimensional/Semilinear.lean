/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Injective and surjective semilinear endomorphisms of finite-dimensional spaces

An injective linear endomorphism of a finite-dimensional vector space is surjective, and vice versa
(`LinearMap.injective_iff_surjective`). The same holds for an endomorphism that is semilinear with
respect to a surjective ring endomorphism `σ` of the scalars:
`LinearMap.surjective_of_injectiveₛₗ` and `LinearMap.injective_of_surjectiveₛₗ`.
Moreover, the descending chain of iterated images `(Submodule.map f)^[n] ⊤` stabilizes by step
`Module.finrank K V`, so `f` restricts to a bijection on
`(Submodule.map f)^[Module.finrank K V] ⊤`.
-/

public section

namespace LinearMap

section SurjectiveInjective

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K} [RingHomSurjective σ]

/-- An injective endomorphism of a finite-dimensional vector space that is semilinear with
respect to a surjective ring endomorphism of the scalars is surjective. -/
theorem surjective_of_injectiveₛₗ {f : V →ₛₗ[σ] V} (hf : Function.Injective f) :
    Function.Surjective f := by
  have hσ : Function.Bijective σ := ⟨σ.injective, RingHomSurjective.is_surjective⟩
  have hrank : Module.rank K V = Module.rank K (range f) :=
    rank_eq_of_equiv_equiv σ
      (AddEquiv.ofBijective f.rangeRestrict.toAddMonoidHom
        ⟨fun x y h => hf (congrArg Subtype.val h), f.surjective_rangeRestrict⟩)
      hσ fun r x => Subtype.ext (map_smulₛₗ f r x)
  rw [← range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (congrArg Cardinal.toNat hrank).symm

/-- A surjective endomorphism of a finite-dimensional vector space that is semilinear with
respect to a surjective ring endomorphism of the scalars is injective. -/
theorem injective_of_surjectiveₛₗ {f : V →ₛₗ[σ] V} (hf : Function.Surjective f) :
    Function.Injective f := by
  have hσ : Function.Bijective σ := ⟨σ.injective, RingHomSurjective.is_surjective⟩
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

/-- On a finite-dimensional vector space, an endomorphism semilinear with respect to a surjective
ring endomorphism of the scalars is injective if and only if it is surjective. -/
theorem injective_iff_surjectiveₛₗ {f : V →ₛₗ[σ] V} :
    Function.Injective f ↔ Function.Surjective f :=
  ⟨surjective_of_injectiveₛₗ, injective_of_surjectiveₛₗ⟩

end SurjectiveInjective

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
theorem iterate_map_top_succ_eq_finrank {K V : Type*} [DivisionRing K] [AddCommGroup V]
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

end LinearMap
