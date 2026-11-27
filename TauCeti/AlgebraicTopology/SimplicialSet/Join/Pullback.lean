/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.Fiber

/-!
# Pullbacks of simplicial joins

Joining two pullback squares produces a pullback square (`SSet.join.isPullback_map`). The
square formed by a map of joins and either factor inclusion is also a pullback
(`SSet.join.isPullback_inl_map`, `SSet.join.isPullback_inr_map`). These identify the factors
of a join as pullbacks of the factors in its base, including when the base is a join of
standard simplices.

There is no monomorphism or quasicategory hypothesis on the component maps. The construction
uses the relative universal property of the join, reducing the lift problem to two independent
lift problems on vertex fibres.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.8 (the simplicial join).
-/

public section

open CategoryTheory Limits

universe u

namespace SSet.join

variable {K L K' L' : SSet.{u}}

/-- The square formed by a map of joins and its left inclusion is a pullback. -/
lemma isPullback_inl_map (f : K ⟶ K') (g : L ⟶ L') :
    IsPullback f (inl K L) (inl K' L') (map f g) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (inl_map f g).symm n, ?_, ?_⟩
  · intro x y h
    exact ((mono_iff_injective ((inl K L).app n)).1 inferInstance) h.2
  · intro y x h
    have hx : (map f g).app n x ∈ (Subcomplex.range (inl K' L')).obj n := ⟨y, h⟩
    have hx' : x ∈ (Subcomplex.range (inl K L)).obj n := by
      rwa [← preimage_range_inl_map f g]
    obtain ⟨z, hz⟩ := hx'
    refine ⟨z, ?_, hz⟩
    apply (mono_iff_injective ((inl K' L').app n)).1 inferInstance
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (inl_map f g).symm n) z).trans
      ((congrArg ((map f g).app n) hz).trans h.symm)

/-- The square formed by a map of joins and its right inclusion is a pullback. -/
lemma isPullback_inr_map (f : K ⟶ K') (g : L ⟶ L') :
    IsPullback g (inr K L) (inr K' L') (map f g) := by
  apply IsPullback.of_forall_isPullback_app
  intro n
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (inr_map f g).symm n, ?_, ?_⟩
  · intro x y h
    exact ((mono_iff_injective ((inr K L).app n)).1 inferInstance) h.2
  · intro y x h
    have hx : (map f g).app n x ∈ (Subcomplex.range (inr K' L')).obj n := ⟨y, h⟩
    have hx' : x ∈ (Subcomplex.range (inr K L)).obj n := by
      rwa [← preimage_range_inr_map f g]
    obtain ⟨z, hz⟩ := hx'
    refine ⟨z, ?_, hz⟩
    apply (mono_iff_injective ((inr K' L').app n)).1 inferInstance
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (inr_map f g).symm n) z).trans
      ((congrArg ((map f g).app n) hz).trans h.symm)

section pullback

variable {X : SSet.{u}}

variable {K₀ K₁ K₂ K₃ L₀ L₁ L₂ L₃ : SSet.{u}}
    {a₀ : K₀ ⟶ K₁} {a₁ : K₀ ⟶ K₂} {f₀ : K₁ ⟶ K₃} {f₁ : K₂ ⟶ K₃}
    {b₀ : L₀ ⟶ L₁} {b₁ : L₀ ⟶ L₂} {g₀ : L₁ ⟶ L₃} {g₁ : L₂ ⟶ L₃}

private lemma exists_pullbackData (hK : IsPullback a₀ a₁ f₀ f₁)
    (hL : IsPullback b₀ b₁ g₀ g₁) (d₀ : JoinData X K₁ L₁) (d₁ : JoinData X K₂ L₂)
    (h : d₀.postcomp f₀ g₀ = d₁.postcomp f₁ g₁) :
    ∃ d : JoinData X K₀ L₀, d.postcomp a₀ b₀ = d₀ ∧ d.postcomp a₁ b₁ = d₁ := by
  let d := d₀.postcomp f₀ g₀
  let e₀ : {e : JoinData X K₁ L₁ // e.postcomp f₀ g₀ = d} := ⟨d₀, rfl⟩
  let e₁ : {e : JoinData X K₂ L₂ // e.postcomp f₁ g₁ = d} := ⟨d₁, h.symm⟩
  let ab₀ := JoinData.postcompEquiv f₀ g₀ d e₀
  let ab₁ := JoinData.postcompEquiv f₁ g₁ d e₁
  have hl : ab₀.1.val ≫ f₀ = ab₁.1.val ≫ f₁ := ab₀.1.property.trans ab₁.1.property.symm
  have hr : ab₀.2.val ≫ g₀ = ab₁.2.val ≫ g₁ := ab₀.2.property.trans ab₁.2.property.symm
  refine ⟨⟨d.p, hK.lift ab₀.1.val ab₁.1.val hl, hL.lift ab₀.2.val ab₁.2.val hr⟩, ?_, ?_⟩
  · rw [JoinData.postcomp_mk, hK.lift_fst, hL.lift_fst]
    have he := congrArg Subtype.val ((JoinData.postcompEquiv f₀ g₀ d).symm_apply_apply e₀)
    simpa only [JoinData.postcompEquiv_symm_coe] using he
  · rw [JoinData.postcomp_mk, hK.lift_snd, hL.lift_snd]
    have he := congrArg Subtype.val ((JoinData.postcompEquiv f₁ g₁ d).symm_apply_apply e₁)
    simpa only [JoinData.postcompEquiv_symm_coe] using he

private lemma pullbackData_ext (hK : IsPullback a₀ a₁ f₀ f₁)
    (hL : IsPullback b₀ b₁ g₀ g₁) {d e : JoinData X K₀ L₀}
    (h₀ : d.postcomp a₀ b₀ = e.postcomp a₀ b₀)
    (h₁ : d.postcomp a₁ b₁ = e.postcomp a₁ b₁) : d = e := by
  obtain ⟨p, l, r⟩ := d
  obtain ⟨q, l', r'⟩ := e
  obtain rfl : p = q := by simpa only [JoinData.postcomp_p] using congrArg JoinData.p h₀
  rw [JoinData.postcomp_mk, JoinData.postcomp_mk] at h₀ h₁
  have hl : l = l' := hK.hom_ext
    (by ext n ⟨x, hx⟩; exact JoinData.congr_left_app h₀ x hx hx)
    (by ext n ⟨x, hx⟩; exact JoinData.congr_left_app h₁ x hx hx)
  have hr : r = r' := hL.hom_ext
    (by ext n ⟨x, hx⟩; exact JoinData.congr_right_app h₀ x hx hx)
    (by ext n ⟨x, hx⟩; exact JoinData.congr_right_app h₁ x hx hx)
  subst hl hr
  rfl

/-- Joining two pullback squares gives a pullback square. Thus the join bifunctor preserves
pullbacks, even when both variables vary. It need not preserve the terminal object. -/
lemma isPullback_map (hK : IsPullback a₀ a₁ f₀ f₁) (hL : IsPullback b₀ b₁ g₀ g₁) :
    IsPullback (map a₀ b₀) (map a₁ b₁) (map f₀ g₀) (map f₁ g₁) := by
  have hw : map a₀ b₀ ≫ map f₀ g₀ = map a₁ b₁ ≫ map f₁ g₁ := by
    rw [← map_comp, ← map_comp, hK.w, hL.w]
  have hlift (s : PullbackCone (map f₀ g₀) (map f₁ g₁)) :
      ∃ F : s.pt ⟶ join K₀ L₀, F ≫ map a₀ b₀ = s.fst ∧ F ≫ map a₁ b₁ = s.snd := by
    obtain ⟨d, hd₀, hd₁⟩ := exists_pullbackData hK hL (homEquiv s.fst) (homEquiv s.snd)
      (by simp only [← homEquiv_comp_map, s.condition])
    exact ⟨homEquiv.symm d, homEquiv.injective (by simp [hd₀]),
      homEquiv.injective (by simp [hd₁])⟩
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s ↦ (hlift s).choose) (fun s ↦ (hlift s).choose_spec.1)
    (fun s ↦ (hlift s).choose_spec.2) (fun s m hm₀ hm₁ ↦ ?_))
  apply homEquiv.injective
  apply pullbackData_ext hK hL
  · simp only [← homEquiv_comp_map, hm₀, (hlift s).choose_spec.1]
  · simp only [← homEquiv_comp_map, hm₁, (hlift s).choose_spec.2]

end pullback

end SSet.join
