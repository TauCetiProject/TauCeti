/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Product.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Ray

/-!
# Rays of product fans

When both factors are nonempty, every ray of a product fan comes from exactly one factor: it is
the product of a ray in that factor with the zero cone in the other. This file gives the two
canonical ray embeddings and proves that their ranges cover all rays of the product fan.

These embeddings index the two families of boundary components in a product toric variety.

## Main declarations

* `TauCeti.Toric.Fan.prodRayInl`: include a ray from the first factor in a product fan.
* `TauCeti.Toric.Fan.prodRayInr`: include a ray from the second factor in a product fan.
* `TauCeti.Toric.Fan.prodRayInl_ne_prodRayInr`: the two families of product rays are disjoint.
* `TauCeti.Toric.Fan.exists_eq_prodRayInl_or_eq_prodRayInr`: every product-fan ray belongs to
  one of these two families.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1--3.2.
-/

public section

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V} {i' : N' →+ V'}
  (Phi : Fan i) (Psi : Fan i')

/-- Include a ray of the first fan as its product with the zero cone of a nonempty second fan. -/
def prodRayInl (hPsi : Nonempty Psi.cones) : Phi.Ray ↪ (Phi.prod Psi).Ray where
  toFun rho :=
    ⟨Phi.prodCone Psi rho.toCone ⟨⊥, Psi.bot_mem hPsi.some.2⟩,
      (PointedCone.finrank_span_coe_prod_bot rho.toCone.1).trans rho.2⟩
  inj' := by
    intro rho rho' h
    apply Subtype.ext
    apply Subtype.ext
    ext x
    have hc : rho.toCone.1.prod (⊥ : PointedCone ℝ V') =
        rho'.toCone.1.prod ⊥ := congrArg (fun r ↦ r.toCone.1) h
    constructor
    · intro hx
      have hpair : (x, 0) ∈ rho'.toCone.1.prod (⊥ : PointedCone ℝ V') := by
        rw [← hc]
        exact ⟨hx, by simp⟩
      exact hpair.1
    · intro hx
      have hpair : (x, 0) ∈ rho.toCone.1.prod (⊥ : PointedCone ℝ V') := by
        rw [hc]
        exact ⟨hx, by simp⟩
      exact hpair.1

/-- The cone underlying a ray included from the first fan is the product of that ray with the
zero cone. -/
@[simp]
theorem toCone_prodRayInl (hPsi : Nonempty Psi.cones) (rho : Phi.Ray) :
    (Phi.prodRayInl Psi hPsi rho).toCone.1 =
      rho.toCone.1.prod (⊥ : PointedCone ℝ V') :=
  (rfl)

/-- A ray included from the first fan lies in a product cone exactly when its original ray lies
in the first factor. -/
@[simp]
theorem prodRayInl_toCone_le_prodCone_iff (hPsi : Nonempty Psi.cones) (rho : Phi.Ray)
    (sigma : Phi.cones) (tau : Psi.cones) :
    (Phi.prodRayInl Psi hPsi rho).toCone ≤ Phi.prodCone Psi sigma tau ↔
      rho.toCone ≤ sigma := by
  rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe, coe_prodCone, toCone_prodRayInl]
  constructor
  · intro h x hx
    have hp : (x, (0 : V')) ∈ rho.toCone.1.prod (⊥ : PointedCone ℝ V') :=
      ⟨hx, rfl⟩
    exact (h hp).1
  · intro h x hx
    rcases x with ⟨x, y⟩
    rcases hx.2 with rfl
    exact ⟨h hx.1, tau.1.zero_mem⟩

/-- Include a ray of the second fan as the product of the zero cone with that ray. -/
def prodRayInr (hPhi : Nonempty Phi.cones) : Psi.Ray ↪ (Phi.prod Psi).Ray where
  toFun rho :=
    ⟨Phi.prodCone Psi ⟨⊥, Phi.bot_mem hPhi.some.2⟩ rho.toCone,
      (PointedCone.finrank_span_coe_bot_prod rho.toCone.1).trans rho.2⟩
  inj' := by
    intro rho rho' h
    apply Subtype.ext
    apply Subtype.ext
    ext x
    have hc : (⊥ : PointedCone ℝ V).prod rho.toCone.1 =
        (⊥ : PointedCone ℝ V).prod rho'.toCone.1 :=
      congrArg (fun r ↦ r.toCone.1) h
    constructor
    · intro hx
      have hpair : (0, x) ∈ (⊥ : PointedCone ℝ V).prod rho'.toCone.1 := by
        rw [← hc]
        exact ⟨by simp, hx⟩
      exact hpair.2
    · intro hx
      have hpair : (0, x) ∈ (⊥ : PointedCone ℝ V).prod rho.toCone.1 := by
        rw [hc]
        exact ⟨by simp, hx⟩
      exact hpair.2

/-- The cone underlying a ray included from the second fan is the product of the zero cone with
that ray. -/
@[simp]
theorem toCone_prodRayInr (hPhi : Nonempty Phi.cones) (rho : Psi.Ray) :
    (Phi.prodRayInr Psi hPhi rho).toCone.1 =
      (⊥ : PointedCone ℝ V).prod rho.toCone.1 :=
  (rfl)

/-- A ray included from the second fan lies in a product cone exactly when its original ray lies
in the second factor. -/
@[simp]
theorem prodRayInr_toCone_le_prodCone_iff (hPhi : Nonempty Phi.cones) (rho : Psi.Ray)
    (sigma : Phi.cones) (tau : Psi.cones) :
    (Phi.prodRayInr Psi hPhi rho).toCone ≤ Phi.prodCone Psi sigma tau ↔
      rho.toCone ≤ tau := by
  rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe, coe_prodCone, toCone_prodRayInr]
  constructor
  · intro h x hx
    have hp : ((0 : V), x) ∈ (⊥ : PointedCone ℝ V).prod rho.toCone.1 :=
      ⟨rfl, hx⟩
    exact (h hp).2
  · intro h x hx
    rcases x with ⟨x, y⟩
    rcases hx.1 with rfl
    exact ⟨sigma.1.zero_mem, h hx.2⟩

/-- A product ray included from the first factor never equals one included from the second
factor. Thus the two canonical families of product-fan rays are disjoint. -/
theorem prodRayInl_ne_prodRayInr (hPhi : Nonempty Phi.cones) (hPsi : Nonempty Psi.cones)
    (rho : Phi.Ray) (tau : Psi.Ray) :
    Phi.prodRayInl Psi hPsi rho ≠ Phi.prodRayInr Psi hPhi tau := by
  intro h
  apply rho.toCone_ne_bot
  apply le_antisymm
  · intro x hx
    have hpair : (x, (0 : V')) ∈
        (Phi.prodRayInr Psi hPhi tau).toCone.1 := by
      rw [← h, Phi.toCone_prodRayInl Psi hPsi]
      exact ⟨hx, rfl⟩
    rw [Phi.toCone_prodRayInr Psi hPhi] at hpair
    exact hpair.1
  · exact bot_le

/-- Every ray of a product of nonempty fans is a ray from exactly one factor, included by taking
its product with the zero cone in the other factor. -/
theorem exists_eq_prodRayInl_or_eq_prodRayInr (hPhi : Nonempty Phi.cones)
    (hPsi : Nonempty Psi.cones) (rho : (Phi.prod Psi).Ray) :
    (∃ r, rho = Phi.prodRayInl Psi hPsi r) ∨ ∃ r, rho = Phi.prodRayInr Psi hPhi r := by
  obtain ⟨sigma, tau, hprod⟩ := Phi.exists_prodCone_eq Psi rho.toCone
  let G : ToricRay (sigma.1.prod tau.1) :=
    rho.toToricRay (Phi.prod Psi) (Phi.prodCone Psi sigma tau) (hprod.symm.le)
  rcases hsplit : ToricRay.prodSplit (Phi.isToricCone sigma.2).salient
      (Psi.isToricCone tau.2).salient G with r | r
  · left
    let rPhi : Phi.Ray := Ray.ofToricRay Phi sigma r
    refine ⟨rPhi, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hG : G = ToricRay.prodInl (Psi.isToricCone tau.2).salient r := by
      calc
        G = (ToricRay.prodSplit (Phi.isToricCone sigma.2).salient
              (Psi.isToricCone tau.2).salient).symm
              (ToricRay.prodSplit (Phi.isToricCone sigma.2).salient
                (Psi.isToricCone tau.2).salient G) :=
          ((ToricRay.prodSplit (Phi.isToricCone sigma.2).salient
            (Psi.isToricCone tau.2).salient).symm_apply_apply G).symm
        _ = ToricRay.prodInl (Psi.isToricCone tau.2).salient r := by simp [hsplit]
    calc
      rho.toCone.1 = G.toPointedCone :=
        (Ray.toPointedCone_toToricRay (Phi.prod Psi) rho
          (Phi.prodCone Psi sigma tau) hprod.symm.le).symm
      _ = r.toPointedCone.prod ⊥ := by rw [hG, ToricRay.toPointedCone_prodInl]
      _ = rPhi.toCone.1.prod ⊥ := by rw [Ray.toCone_ofToricRay]
      _ = (Phi.prodRayInl Psi hPsi rPhi).toCone.1 :=
        (Phi.toCone_prodRayInl Psi hPsi rPhi).symm
  · right
    let rPsi : Psi.Ray := Ray.ofToricRay Psi tau r
    refine ⟨rPsi, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have hG : G = ToricRay.prodInr (Phi.isToricCone sigma.2).salient r := by
      calc
        G = (ToricRay.prodSplit (Phi.isToricCone sigma.2).salient
              (Psi.isToricCone tau.2).salient).symm
              (ToricRay.prodSplit (Phi.isToricCone sigma.2).salient
                (Psi.isToricCone tau.2).salient G) :=
          ((ToricRay.prodSplit (Phi.isToricCone sigma.2).salient
            (Psi.isToricCone tau.2).salient).symm_apply_apply G).symm
        _ = ToricRay.prodInr (Phi.isToricCone sigma.2).salient r := by simp [hsplit]
    calc
      rho.toCone.1 = G.toPointedCone :=
        (Ray.toPointedCone_toToricRay (Phi.prod Psi) rho
          (Phi.prodCone Psi sigma tau) hprod.symm.le).symm
      _ = (⊥ : PointedCone ℝ V).prod r.toPointedCone := by
        rw [hG, ToricRay.toPointedCone_prodInr]
      _ = (⊥ : PointedCone ℝ V).prod rPsi.toCone.1 := by rw [Ray.toCone_ofToricRay]
      _ = (Phi.prodRayInr Psi hPhi rPsi).toCone.1 :=
        (Phi.toCone_prodRayInr Psi hPhi rPsi).symm

end TauCeti.Toric.Fan
