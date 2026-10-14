/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic

/-!
# Graded Ext finiteness for quotients

In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, finite internal support of
`Ext(X₁,Y)` and `Ext(X₂,Y)` implies finite internal support of `Ext(X₃,Y)`.
The long exact Ext sequence also bounds the cohomological support of `X₃` one degree
after the bound for `X₁`. This makes a finite projective presentation usable for
graded Euler characteristics.

The argument uses the contravariant long exact Ext sequence of Mathlib, via the linear
maps in `TauCeti.Algebra.Homology.Ext.Basic`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C]
  {k : Type t} [Field k] [Linear k C] [HasExt.{w} C]
  {e : C ≌ C} {S : ShortComplex C} {Y : C}

/-- Finite internal support of graded Ext passes to the quotient term of a short exact
sequence in the first variable. -/
theorem IsGradedExtInternallyFinite.of_shortExact₃' (hS : S.ShortExact)
    (h₁ : IsGradedExtInternallyFinite.{w} k e S.X₁ Y)
    (h₂ : IsGradedExtInternallyFinite.{w} k e S.X₂ Y) :
    IsGradedExtInternallyFinite.{w} k e S.X₃ Y := by
  refine ⟨fun n ↦ ?_⟩
  match n with
  | 0 =>
      exact (h₂.finiteLaurentSupport 0).of_injective
        (fun j ↦ Ext.precompOfLinear (Ext.mk₀ S.g) k ((e ^ j).functor.obj Y) (zero_add 0))
        (fun j ↦ by
          have := hS.epi_g
          simpa only [coe_precompOfLinear] using
            Ext.precomp_mk₀_injective_of_epi ((e ^ j).functor.obj Y) S.g)
  | n + 1 =>
      exact (h₁.finiteLaurentSupport n).of_exact (h₂.finiteLaurentSupport (n + 1))
        (fun j ↦ Ext.precompOfLinear hS.extClass k ((e ^ j).functor.obj Y) (Nat.one_add n))
        (fun j ↦ Ext.precompOfLinear (Ext.mk₀ S.g) k ((e ^ j).functor.obj Y)
          (zero_add (n + 1)))
        (fun j ↦ exact_precompOfLinear₃ k hS ((e ^ j).functor.obj Y) n (n + 1)
          (Nat.one_add n))

/-- If graded Ext from the subobject vanishes from degree `N₁` and from the middle
object from degree `N₂`, then graded Ext from the quotient vanishes from
`max (N₁ + 1) N₂`. -/
theorem IsGradedExtBoundedBy.of_shortExact₃' (hS : S.ShortExact) {N₁ N₂ : ℕ}
    (h₁ : IsGradedExtBoundedBy.{w} e S.X₁ Y N₁)
    (h₂ : IsGradedExtBoundedBy.{w} e S.X₂ Y N₂) :
    IsGradedExtBoundedBy.{w} e S.X₃ Y (max (N₁ + 1) N₂) := by
  refine ⟨fun {m} hm j ↦ ?_⟩
  cases m with
  | zero => omega
  | succ n =>
      have hleft : N₁ ≤ n := by omega
      have hright : N₂ ≤ n + 1 := by omega
      let := h₁.subsingleton hleft j
      let := h₂.subsingleton hright j
      exact subsingleton_of_exact
        (exact_precomp₃ hS ((e ^ j).functor.obj Y) n (n + 1)
          (Nat.one_add n))

/-- Graded Euler admissibility passes from the subobject and the middle object to
the quotient of a short exact sequence. -/
theorem IsGradedEulerAdmissible.of_shortExact₃' (hS : S.ShortExact)
    (h₁ : IsGradedEulerAdmissible.{w} k e S.X₁ Y)
    (h₂ : IsGradedEulerAdmissible.{w} k e S.X₂ Y) :
    IsGradedEulerAdmissible.{w} k e S.X₃ Y := by
  obtain ⟨N₁, hN₁⟩ := h₁.bounded.exists_bound
  obtain ⟨N₂, hN₂⟩ := h₂.bounded.exists_bound
  exact ⟨h₁.internallyFinite.of_shortExact₃' hS h₂.internallyFinite,
    (hN₁.of_shortExact₃' hS hN₂).isGradedExtBounded⟩

end TauCeti
