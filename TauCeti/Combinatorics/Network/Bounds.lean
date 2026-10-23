/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Flow

/-!
# Replacing network bounds

A network's arrow family is independent of its lower and upper bounds.  This file provides the
same-arrow constructions that replace either or both bounds, and transports bounded terminal
assignments and ordinary flows when the feasible interval is enlarged.  In particular, increasing
ordinary capacities preserves every existing flow; this is the comparison used when capacities
are capped or otherwise changed.

The constructions retain arrow identities, including parallel arrows and loops.  They therefore
change only feasibility, never conservation, excess, or flow value.

## Main definitions

* `TauCeti.Network.replaceBounds` replaces both bound functions of a network.
* `TauCeti.Network.replaceLower` and `TauCeti.Network.replaceUpper` replace one bound function.
* `TauCeti.BoundedFlow.mono` regards a bounded terminal assignment as one with weaker bounds.
* `TauCeti.Flow.mono` regards an ordinary flow as one with larger capacities.
-/

public section

namespace TauCeti

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

namespace Network

variable [LE K] (N : Network K V)

/-- Replace both bound functions of a network without changing its vertices or arrows.

This definition is exposed because its arrow family must reduce when assignments on the resulting
network are elaborated. -/
@[expose]
def replaceBounds (lower upper : N.Assignment K)
    (lower_le_upper : ∀ {x y} (e : N.Hom x y), lower e ≤ upper e) : Network K V where
  Hom := N.Hom
  lower := lower
  upper := upper
  lower_le_upper := lower_le_upper

@[simp]
theorem replaceBounds_Hom (lower upper : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), lower e ≤ upper e) :
    (N.replaceBounds lower upper h).Hom = N.Hom :=
  (rfl)

@[simp]
theorem replaceBounds_lower (lower upper : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), lower e ≤ upper e) {x y}
    (e : (N.replaceBounds lower upper h).Hom x y) :
    (N.replaceBounds lower upper h).lower e = lower e :=
  (rfl)

@[simp]
theorem replaceBounds_upper (lower upper : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), lower e ≤ upper e) {x y}
    (e : (N.replaceBounds lower upper h).Hom x y) :
    (N.replaceBounds lower upper h).upper e = upper e :=
  (rfl)

/-- Two replacements of a fixed network agree exactly when both of their bound functions agree. -/
@[simp]
theorem replaceBounds_inj {lower₁ upper₁ lower₂ upper₂ : N.Assignment K}
    {h₁ : ∀ {x y} (e : N.Hom x y), lower₁ e ≤ upper₁ e}
    {h₂ : ∀ {x y} (e : N.Hom x y), lower₂ e ≤ upper₂ e} :
    N.replaceBounds lower₁ upper₁ h₁ = N.replaceBounds lower₂ upper₂ h₂ ↔
      lower₁ = lower₂ ∧ upper₁ = upper₂ := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Replacing a network's bounds by its original bounds does nothing. -/
@[simp]
theorem replaceBounds_self : N.replaceBounds N.lower N.upper N.lower_le_upper = N := by
  cases N
  rfl

/-- A second same-arrow bound replacement discards the first pair of bounds. -/
@[simp]
theorem replaceBounds_replaceBounds (lower upper : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), lower e ≤ upper e)
    (lower' upper' : N.Assignment K)
    (h' : ∀ {x y} (e : N.Hom x y), lower' e ≤ upper' e) :
    (N.replaceBounds lower upper h).replaceBounds lower' upper' h' =
      N.replaceBounds lower' upper' h' :=
  (rfl)

/-- Replace only the lower bounds of a network.

This definition is exposed because its arrow family must reduce when assignments on the resulting
network are elaborated. -/
@[expose]
def replaceLower (lower : N.Assignment K)
    (lower_le_upper : ∀ {x y} (e : N.Hom x y), lower e ≤ N.upper e) : Network K V :=
  N.replaceBounds lower N.upper lower_le_upper

@[simp]
theorem replaceLower_Hom (lower : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), lower e ≤ N.upper e) :
    (N.replaceLower lower h).Hom = N.Hom :=
  (rfl)

@[simp]
theorem replaceLower_lower (lower : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), lower e ≤ N.upper e) {x y}
    (e : (N.replaceLower lower h).Hom x y) :
    (N.replaceLower lower h).lower e = lower e :=
  (rfl)

@[simp]
theorem replaceLower_upper (lower : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), lower e ≤ N.upper e) {x y}
    (e : (N.replaceLower lower h).Hom x y) :
    (N.replaceLower lower h).upper e = N.upper e :=
  (rfl)

@[simp]
theorem replaceLower_self : N.replaceLower N.lower N.lower_le_upper = N :=
  N.replaceBounds_self

/-- Replace only the upper bounds of a network.

This definition is exposed because its arrow family must reduce when assignments on the resulting
network are elaborated. -/
@[expose]
def replaceUpper (upper : N.Assignment K)
    (lower_le_upper : ∀ {x y} (e : N.Hom x y), N.lower e ≤ upper e) : Network K V :=
  N.replaceBounds N.lower upper lower_le_upper

@[simp]
theorem replaceUpper_Hom (upper : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), N.lower e ≤ upper e) :
    (N.replaceUpper upper h).Hom = N.Hom :=
  (rfl)

@[simp]
theorem replaceUpper_lower (upper : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), N.lower e ≤ upper e) {x y}
    (e : (N.replaceUpper upper h).Hom x y) :
    (N.replaceUpper upper h).lower e = N.lower e :=
  (rfl)

@[simp]
theorem replaceUpper_upper (upper : N.Assignment K)
    (h : ∀ {x y} (e : N.Hom x y), N.lower e ≤ upper e) {x y}
    (e : (N.replaceUpper upper h).Hom x y) :
    (N.replaceUpper upper h).upper e = upper e :=
  (rfl)

@[simp]
theorem replaceUpper_self : N.replaceUpper N.upper N.lower_le_upper = N :=
  N.replaceBounds_self

end Network

section BoundedFlow

variable [Fintype V] [∀ x y, Fintype (Q x y)] [AddCommGroup K] [Preorder K]

namespace BoundedFlow

variable {lo hi lo' hi' : Assignment Q K} {s t : V}

/-- A bounded terminal assignment remains feasible after decreasing its lower bounds and increasing
its upper bounds.  Its arrow assignment, conservation equations, and value are unchanged. -/
def mono (f : BoundedFlow lo hi s t) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    BoundedFlow lo' hi' s t where
  toFun := f.toFun
  mem_Icc := Set.Icc_subset_Icc hlo hhi f.mem_Icc
  conserve := f.conserve

@[simp]
theorem mono_toFun (f : BoundedFlow lo hi s t) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    (f.mono hlo hhi).toFun = f.toFun :=
  (rfl)

@[simp]
theorem val_mono (f : BoundedFlow lo hi s t) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    (f.mono hlo hhi).val = f.val :=
  by simp only [BoundedFlow.val_def, mono_toFun]

@[simp]
theorem mono_refl (f : BoundedFlow lo hi s t) : f.mono le_rfl le_rfl = f := by
  ext
  rfl

/-- Weakening bounds twice is the same as weakening them once by the composite inequalities. -/
theorem mono_mono (f : BoundedFlow lo hi s t) {lo'' hi'' : Assignment Q K}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hlo' : lo'' ≤ lo') (hhi' : hi' ≤ hi'') :
    (f.mono hlo hhi).mono hlo' hhi' = f.mono (hlo'.trans hlo) (hhi.trans hhi') := by
  ext
  rfl

end BoundedFlow

namespace Flow

variable {cap cap' : Assignment Q K} {s t : V}

/-- An ordinary flow remains a flow when every arrow capacity is increased.  Its assignment and
value are unchanged. -/
def mono (f : Flow cap s t) (hcap : cap ≤ cap') : Flow cap' s t where
  toBoundedFlow := f.toBoundedFlow.mono le_rfl hcap
  excessAt_sink_nonneg := f.excessAt_sink_nonneg

@[simp]
theorem mono_toFun (f : Flow cap s t) (hcap : cap ≤ cap') :
    (f.mono hcap).toFun = f.toFun :=
  (rfl)

@[simp]
theorem val_mono (f : Flow cap s t) (hcap : cap ≤ cap') :
    (f.mono hcap).val = f.val :=
  by simp only [BoundedFlow.val_def, mono_toFun]

@[simp]
theorem mono_refl (f : Flow cap s t) : f.mono le_rfl = f := by
  ext
  rfl

/-- Increasing capacities twice is the same as increasing them once by transitivity. -/
theorem mono_mono (f : Flow cap s t) {cap'' : Assignment Q K}
    (hcap : cap ≤ cap') (hcap' : cap' ≤ cap'') :
    (f.mono hcap).mono hcap' = f.mono (hcap.trans hcap') := by
  ext
  rfl

end Flow

end BoundedFlow

end TauCeti
