/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.SelfInjective
public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.TopDegree

/-!
# The type-A Koszul defect

For the signless preprojective algebra of `Aₙ`, the kernel of the left vertex Koszul map at
`a.rev` is precisely the line through the top valley from `a` to `a.rev`. Consequently its
graded corner dimensions are one in degree `n - 1` at source `a`, and zero everywhere else.
This identifies both the degree and the vertex permutation of the almost-Koszul defect.

The top valleys and the Frobenius functional come from the type-A top-degree and
self-injectivity modules. Use `mem_ker_signlessPreprojectiveKoszulLeft_A_iff` to express
elements of the left-end defect of the vertex Koszul complex as scalar multiples of the top
valley. The finrank formulas give its total dimension and locate its unique nonzero graded
corner, specifying the defect degree and vertex permutation.

These statements hold over every field, including characteristic two, and include `A₁`.
They concern the signless algebra of the doubled graph; no orientation or quadratic zigzag
presentation is chosen.

## References

* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), Sections 3 and 4.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the type-A Nakayama permutation.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver MulOpposite

variable (k : Type*) [Field k] {n : ℕ}

attribute [local instance] finiteNeighborSetFintype signlessPreprojectiveGradedAlgebra

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "Q" => DoubledQuiver AG
local notation "Π" => signlessPreprojectiveAlgebra k Q
local notation "σ" => signlessPreprojectiveMk k Q
local notation "φ" => signlessPreprojectiveAFrobeniusFunctional k (n := n)
local notation "e" => fun a : Fin (DynkinType.A n).rank => σ (vertexIdempotent k (vertex AG a))

/-- On a left Koszul kernel, vanishing of the Frobenius functional forces vanishing. -/
private theorem eq_zero_of_frobenius_eq_zero (a : Fin (DynkinType.A n).rank) {x : Π}
    (hx : e a * x = x)
    (hb : ∀ (i : Q) (b : vertex AG a ⟶ i), σ (ofArrow b) * x = 0)
    (hφ : φ x = 0) : x = 0 := by
  apply (isFrobeniusFunctional_signlessPreprojectiveAFrobeniusFunctional k).eq_zero_of_forall_right
  intro r
  obtain ⟨p, rfl⟩ := signlessPreprojectiveMk_surjective k Q r
  have hvertex (i : Q) : φ (σ (vertexIdempotent k i) * x) = 0 := by
    by_cases hi : i = vertex AG a
    · subst i
      rw [hx, hφ]
    · rw [← hx, ← mul_assoc, ← map_mul,
        vertexIdempotent_mul_vertexIdempotent_of_ne hi, map_zero, zero_mul, map_zero]
  have harrow {i j : Q} (b : i ⟶ j) : σ (ofArrow b) * x = 0 := by
    by_cases hi : i = vertex AG a
    · subst i
      exact hb j b
    · rw [← hx, ← mul_assoc, ← map_mul, ofArrow_eq_ofPath,
        ofPath_mul_vertexIdempotent_of_ne _ (Ne.symm hi), map_zero, zero_mul]
  have hkill : ∀ {i j : Q} (p : Path i j), 0 < p.length → σ (ofPath ⟨i, j, p⟩) * x = 0 := by
    intro i j p hp
    induction p with
    | nil => exact absurd hp (lt_irrefl 0)
    | cons p c ih =>
      cases p with
      | nil => simpa only [ofArrow_eq_ofPath, Hom.toPath] using harrow c
      | cons p d =>
        rw [← ofArrow_mul_ofPath, map_mul, mul_assoc,
          ih (by simp only [Path.length_cons]; omega), mul_zero]
  induction p using PathAlgebra.induction_linear with
  | zero => rw [map_zero, zero_mul, map_zero]
  | add p q hp hq => simp only [map_add, add_mul, hp, hq, add_zero]
  | single p c =>
    rw [single_eq_smul_ofPath, map_smul, smul_mul_assoc, map_smul]
    suffices h : φ (σ (ofPath p) * x) = 0 by rw [h, smul_zero]
    obtain ⟨i, j, p⟩ := p
    cases p with
    | nil => simpa only [vertexIdempotent_eq_ofPath] using hvertex i
    | cons p b => rw [hkill _ (by simp only [Path.length_cons]; omega), map_zero]

/-- The Frobenius functional reads the coefficient in the top-valley line. -/
private theorem eq_smul_topValley (a : Fin (DynkinType.A n).rank) {x : Π}
    (hx : e a.rev * x = x)
    (hb : ∀ (i : Q) (b : vertex AG a.rev ⟶ i), σ (ofArrow b) * x = 0) :
    x = φ x • signlessPreprojectiveAValley k a a.rev 0 := by
  have hy := signlessPreprojectiveAValley_zero_mem_top_corner k a
  have hφ : φ (signlessPreprojectiveAValley k a a.rev 0) = 1 := by
    rw [signlessPreprojectiveAFrobeniusFunctional_valley]
    · simp
    · have ha := a.isLt
      have hn := DynkinType.rank_A n
      simp only [Finset.mem_Icc, Fin.val_rev]
      omega
  apply sub_eq_zero.mp
  apply eq_zero_of_frobenius_eq_zero k a.rev
  · rw [mul_sub, mul_smul_comm,
      signlessPreprojectiveMk_vertexIdempotent_mul_of_mem_signlessPreprojectiveCorner hy, hx]
  · intro i b
    rw [mul_sub, mul_smul_comm, hb i b,
      signlessPreprojectiveMk_ofArrow_mul_AValley_zero, smul_zero, sub_self]
  · rw [map_sub, map_smul, hφ, smul_eq_mul, mul_one, sub_self]

/-- The left Koszul kernel of `Aₙ` at `a.rev` is exactly the line through the top valley from
`a` to `a.rev`. In particular, this determines its Nakayama vertex as well as its generator. -/
theorem mem_ker_signlessPreprojectiveKoszulLeft_A_iff
    (a : Fin (DynkinType.A n).rank)
    (x : signlessPreprojectiveRightProjective k (vertex AG a.rev)) :
    x ∈ LinearMap.ker (signlessPreprojectiveKoszulLeft k (vertex AG a.rev)) ↔
      ∃ t : k, x = t • signlessPreprojectiveATopValley k a := by
  constructor
  · intro hx
    have hb (i : Q) (b : vertex AG a.rev ⟶ i) : σ (ofArrow b) * unop (x : Πᵐᵒᵖ) = 0 := by
      have h := congrArg (fun z => unop (z i (Quiver.reverse b) : Πᵐᵒᵖ))
        (LinearMap.mem_ker.mp hx)
      simpa only [unop_signlessPreprojectiveKoszulLeft_apply, reverse_reverse, Pi.zero_apply,
        Submodule.coe_zero, unop_zero] using h
    refine ⟨φ (unop (x : Πᵐᵒᵖ)), Subtype.ext (unop_injective ?_)⟩
    simpa only [Submodule.coe_smul_of_tower, unop_smul, unop_signlessPreprojectiveATopValley] using
      eq_smul_topValley k a ((mem_signlessPreprojectiveRightProjective_iff k _ _).1 x.2) hb
  · rintro ⟨t, rfl⟩
    exact ((LinearMap.ker (signlessPreprojectiveKoszulLeft k
      (vertex AG a.rev))).restrictScalars k).smul_mem t
        (signlessPreprojectiveATopValley_mem_ker k a)

/-- The full left Koszul kernel of `Aₙ` at each vertex is one-dimensional. -/
@[simp]
theorem finrank_ker_signlessPreprojectiveKoszulLeft_A
    (a : Fin (DynkinType.A n).rank) :
    Module.finrank k (LinearMap.ker (signlessPreprojectiveKoszulLeft k (vertex AG a.rev))) = 1 := by
  let y : LinearMap.ker (signlessPreprojectiveKoszulLeft k (vertex AG a.rev)) :=
    ⟨signlessPreprojectiveATopValley k a, signlessPreprojectiveATopValley_mem_ker k a⟩
  refine (finrank_eq_one_iff_of_nonzero' y (fun h =>
    signlessPreprojectiveATopValley_ne_zero k a (congrArg Subtype.val h))).2 fun x => ?_
  obtain ⟨t, ht⟩ := (mem_ker_signlessPreprojectiveKoszulLeft_A_iff k a x.1).1 x.2
  exact ⟨t, Subtype.ext ht.symm⟩

/-- The graded Koszul defect of `Aₙ` at `a.rev` is the degree-`n - 1` line with source `a`.
Every other graded corner of the kernel vanishes. -/
@[simp]
theorem finrank_signlessPreprojectiveCorner_inf_iInf_ker_A
    (a : Fin (DynkinType.A n).rank) (m : ℕ) (i : Fin (DynkinType.A n).rank) :
    Module.finrank k ↥(signlessPreprojectiveCorner k Q m (vertex AG i) (vertex AG a.rev) ⊓
      ⨅ (w : Q) (b : w ⟶ vertex AG a.rev),
        LinearMap.ker (LinearMap.mulLeft k (σ (ofArrow (Quiver.reverse b))))) =
      if m = n - 1 ∧ i = a then 1 else 0 := by
  classical
  let y := signlessPreprojectiveAValley k a a.rev 0
  have hy := signlessPreprojectiveAValley_zero_mem_top_corner k a
  have hy0 : y ≠ 0 := signlessPreprojectiveAValley_zero_ne_zero k a
  have hK {x : Π} (hx : x ∈ signlessPreprojectiveCorner k Q m (vertex AG i) (vertex AG a.rev) ⊓
      ⨅ (w : Q) (b : w ⟶ vertex AG a.rev),
        LinearMap.ker (LinearMap.mulLeft k (σ (ofArrow (Quiver.reverse b))))) :
      ∃ t : k, x = t • y := by
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.mulLeft_apply] at hx
    exact ⟨φ x, eq_smul_topValley k a
      (signlessPreprojectiveMk_vertexIdempotent_mul_of_mem_signlessPreprojectiveCorner hx.1)
      (fun w b => by simpa only [reverse_reverse] using hx.2 w (Quiver.reverse b))⟩
  split_ifs with h
  · obtain ⟨hm, hi⟩ := h
    subst m i
    have hyK : y ∈ signlessPreprojectiveCorner k Q (n - 1) (vertex AG a) (vertex AG a.rev) ⊓
        ⨅ (w : Q) (b : w ⟶ vertex AG a.rev),
          LinearMap.ker (LinearMap.mulLeft k (σ (ofArrow (Quiver.reverse b)))) := by
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact ⟨hy, fun w b => signlessPreprojectiveMk_ofArrow_mul_AValley_zero k a _⟩
    refine (finrank_eq_one_iff' (K := k)).2 ⟨⟨y, hyK⟩,
      fun hz => hy0 (congrArg Subtype.val hz), fun x => ?_⟩
    obtain ⟨t, ht⟩ := hK x.2
    exact ⟨t, Subtype.ext ht.symm⟩
  · rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨t, rfl⟩ := hK hx
    by_contra hx0
    have ht : t ≠ 0 := fun ht => hx0 (by rw [ht, zero_smul])
    have hy' : y ∈ signlessPreprojectiveCorner k Q m (vertex AG i) (vertex AG a.rev) := by
      simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using
        Submodule.smul_mem _ t⁻¹ (Submodule.mem_inf.1 hx).1
    refine hy0 (Submodule.disjoint_def.1 (disjoint_signlessPreprojectiveCorner ?_) y hy' hy)
    by_cases hm : m = n - 1
    · exact Or.inr (Or.inl fun hi => h ⟨hm, (vertex_injective AG) hi⟩)
    · exact Or.inl hm

end TauCeti
