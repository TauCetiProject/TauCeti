/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# Homotopy with a predicate is path connectedness

Mathlib's `ContinuousMap.HomotopicWith f g P` asks for a homotopy from `f` to `g` all of whose
stages satisfy `P`. This file proves that, when the domain is locally compact, this is exactly
path connectedness of `f` and `g` in the subspace `{h : C(X, Y) // P h}` of the compact-open
topology: currying a homotopy gives the path, and uncurrying a path gives the homotopy.

## Main declarations

* `ContinuousMap.homotopicWith_iff_joined`: `f.HomotopicWith g P` holds exactly when `f` and `g`
  are joined by a path in `{h : C(X, Y) // P h}`.
-/

public section


namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P : C(X, Y) → Prop}

/-- **Homotopy through maps satisfying `P` is path connectedness in `{h : C(X, Y) // P h}`**,
for a locally compact domain. -/
theorem homotopicWith_iff_joined [LocallyCompactSpace X] {f g : C(X, Y)} (hf : P f) (hg : P g) :
    f.HomotopicWith g P ↔ Joined (⟨f, hf⟩ : {h // P h}) ⟨g, hg⟩ := by
  refine ⟨fun ⟨F⟩ => ⟨?_⟩, fun ⟨γ⟩ => ⟨?_⟩⟩
  · exact
      { toFun t := ⟨F.toContinuousMap.curry t, F.prop t⟩
        continuous_toFun := (map_continuous F.toContinuousMap.curry).subtype_mk _
        source' := Subtype.ext <| ContinuousMap.ext fun x => F.apply_zero x
        target' := Subtype.ext <| ContinuousMap.ext fun x => F.apply_one x }
  · exact
      { toFun := ContinuousMap.uncurry
          ((⟨Subtype.val, continuous_subtype_val⟩ : C({h // P h}, C(X, Y))).comp γ.toContinuousMap)
        map_zero_left x := congrArg (fun r : {h // P h} => r.1 x) γ.source
        map_one_left x := congrArg (fun r : {h // P h} => r.1 x) γ.target
        prop' t := (γ t).2 }

end ContinuousMap
