/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Sigma
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Paths and homotopies in a disjoint union

A path in a disjoint union `Σ i, X i` never leaves the summand it starts in, because the unit
interval is connected: this is Mathlib's `ContinuousMap.exists_lift_sigma`. This file draws the
consequences that the fundamental groupoid of a disjoint union needs: the two endpoints of a path
lie in the same summand, and a path between two points of the `i`-th summand is the image of a
path in that summand; both also for path homotopy classes.

In the other direction, maps out of a disjoint union are homotopic as soon as their restrictions
to the summands are: homotopies of the summands glue to a homotopy of the map they define
(`ContinuousMap.Homotopy.sigma`). Since the summands are open, no compatibility between the
homotopies is needed.

The inclusion of a summand is spelled out as the anonymous bundled map
`⟨Sigma.mk i, continuous_sigmaMk⟩` rather than `ContinuousMap.sigmaMk i`, because only the former
has an application that reduces definitionally, which the dependently typed rewrites downstream
need.

## Main declarations

* `Path.sigma_fst_eq`: the endpoints of a path in a disjoint union lie in the same summand.
* `Path.exists_map_sigmaMk_eq`: **a path between two points of the `i`-th summand is the image
  of a path in that summand.**
* `Path.Homotopic.Quotient.sigma_fst_eq`, `Path.Homotopic.Quotient.exists_map_sigmaMk_eq`: the
  same for path homotopy classes.
* `ContinuousMap.Homotopy.sigma` and `ContinuousMap.Homotopic.sigma`: homotopies of the summands of
  a map out of a disjoint union glue to a homotopy of the map.
-/

public section

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

namespace Path

/-- The endpoints of a path in a disjoint union lie in the same summand. -/
theorem sigma_fst_eq {x y : Σ i, X i} (γ : Path x y) : x.1 = y.1 := by
  obtain ⟨j, g, hg⟩ := ContinuousMap.exists_lift_sigma γ.toContinuousMap
  have hγ : ∀ t, (γ t).1 = j := fun t => congrArg Sigma.fst (DFunLike.congr_fun hg t)
  simpa using (hγ 0).trans (hγ 1).symm

/-- **A path between two points of the `i`-th summand of a disjoint union is the image of a path
in that summand.** -/
theorem exists_map_sigmaMk_eq {i : ι} {x y : X i} (γ : Path (⟨i, x⟩ : Σ j, X j) ⟨i, y⟩) :
    ∃ γ' : Path x y, γ'.map continuous_sigmaMk = γ := by
  obtain ⟨j, g, hg⟩ := ContinuousMap.exists_lift_sigma γ.toContinuousMap
  have hγ : ∀ t, γ t = ⟨j, g t⟩ := fun t => DFunLike.congr_fun hg t
  obtain rfl : j = i := congrArg Sigma.fst ((hγ 0).symm.trans γ.source)
  exact ⟨⟨g, sigma_mk_injective ((hγ 0).symm.trans γ.source),
    sigma_mk_injective ((hγ 1).symm.trans γ.target)⟩, Path.ext (funext fun t => (hγ t).symm)⟩

namespace Homotopic.Quotient

/-- The endpoints of a path homotopy class in a disjoint union lie in the same summand. -/
theorem sigma_fst_eq {x y : Σ i, X i} (γ : Path.Homotopic.Quotient x y) : x.1 = y.1 := by
  obtain ⟨γ⟩ := γ
  exact γ.sigma_fst_eq

/-- **A path homotopy class between two points of the `i`-th summand of a disjoint union is the
image of a class in that summand.** -/
theorem exists_map_sigmaMk_eq {i : ι} {x y : X i}
    (γ : Path.Homotopic.Quotient (⟨i, x⟩ : Σ j, X j) ⟨i, y⟩) :
    ∃ γ' : Path.Homotopic.Quotient x y,
      γ'.map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)) = γ := by
  obtain ⟨γ⟩ := γ
  obtain ⟨γ', hγ'⟩ := γ.exists_map_sigmaMk_eq
  exact ⟨Path.Homotopic.Quotient.mk γ', by rw [← Path.Homotopic.Quotient.mk_map, hγ']; rfl⟩

end Homotopic.Quotient

end Path

namespace ContinuousMap

open unitInterval

variable {Y : Type*} [TopologicalSpace Y] {f g : ∀ i, C(X i, Y)}

/-- **Homotopies of the summands glue.** A family of homotopies `f i ≃ g i` of maps out of the
summands of a disjoint union is a homotopy of the maps `ContinuousMap.sigma f` and
`ContinuousMap.sigma g` out of the disjoint union. -/
def Homotopy.sigma (H : ∀ i, (f i).Homotopy (g i)) :
    (ContinuousMap.sigma f).Homotopy (ContinuousMap.sigma g) where
  toFun p := H p.2.1 (p.1, p.2.2)
  -- Through `I × Σ i, X i ≃ₜ Σ i, X i × I`, the map is `H i ∘ swap` on the `i`-th summand.
  continuous_toFun := by
    have : Continuous fun q : Σ i, X i × I ↦ H q.1 (q.2.2, q.2.1) :=
      continuous_sigma fun i ↦
        ((H i).continuous.comp continuous_swap : Continuous fun q : X i × I ↦ H i (q.2, q.1))
    exact this.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)
  map_zero_left x := (H x.1).apply_zero x.2
  map_one_left x := (H x.1).apply_one x.2

@[simp]
theorem Homotopy.sigma_apply (H : ∀ i, (f i).Homotopy (g i)) (t : I) (i : ι) (x : X i) :
    Homotopy.sigma H (t, ⟨i, x⟩) = H i (t, x) :=
  (rfl)

/-- Maps out of a disjoint union whose restrictions to the summands are homotopic are
homotopic. -/
theorem Homotopic.sigma (h : ∀ i, (f i).Homotopic (g i)) :
    (ContinuousMap.sigma f).Homotopic (ContinuousMap.sigma g) :=
  ⟨Homotopy.sigma fun i ↦ (h i).some⟩

end ContinuousMap
