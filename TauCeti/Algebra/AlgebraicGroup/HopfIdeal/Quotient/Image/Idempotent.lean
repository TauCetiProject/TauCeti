/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Images of idempotent affine-group endomorphisms

The image of an idempotent endomorphism is its fixed subgroup, scheme-theoretically:
the coordinate image factorization splits, and its points over every commutative test
algebra are exactly the fixed points. In particular this applies to regular Jordan
projections of commutative affine groups.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15–16.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k}

/-- The coordinate image factorization of an idempotent endomorphism is a retraction. -/
@[simp]
theorem imageι_comp_mkImage_of_idempotent (f : H ⟶ H) (hf : f ≫ f = f) :
    imageι f ≫ mkImage f = 𝟙 (image f) := by
  apply (cancel_epi (mkImage f)).mp
  apply (cancel_mono (imageι f)).mp
  simpa only [Category.assoc, Category.comp_id, Category.id_comp,
    mkImage_comp_imageι, mkImage_comp_imageι_assoc] using hf

/-- The image of an idempotent affine-group endomorphism represents its fixed points over
all commutative test algebras, including nonreduced algebras. -/
@[simp]
theorem mem_quotientPointsSubgroup_ker_iff_mapDomain_eq_self (f : H ⟶ H)
    (hf : f ≫ f = f) (A : CommAlgCat.{w} k) (g : WithConv (H →ₐ[k] A)) :
    g ∈ quotientPointsSubgroup H (HopfIdeal.ker f.hom) A ↔
      BialgHom.mapDomain f.hom g = g := by
  rw [mem_quotientPointsSubgroup_iff]
  constructor
  · intro hg
    apply ofConv_injective
    ext x
    rw [BialgHom.mapDomain_apply_apply]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hg
    rw [HopfIdeal.mem_ker, map_sub, sub_eq_zero]
    exact congrArg (fun h : H ⟶ H ↦ h.hom x) hf
  · intro hg x hx
    rw [HopfIdeal.mem_ker] at hx
    have h := congrArg (fun p : WithConv (H →ₐ[k] A) ↦ p.ofConv x) hg
    simpa only [BialgHom.mapDomain_apply_apply, hx, map_zero] using h.symm

end TauCeti.CommHopfAlgCat
