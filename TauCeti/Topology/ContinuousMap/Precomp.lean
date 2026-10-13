/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Precomposition with a surjection from a compact space

If `q : A → B` is a continuous surjection from a compact space `A` to a Hausdorff space `B`, then
precomposition with `q` embeds the space `C(B, X)` of continuous maps, with the compact-open
topology, in `C(A, X)`. The reason is that the preimage of a compact subset of `B` under `q` is
closed, hence compact, so every subbasic compact-open condition on `B` is the pullback of a
subbasic compact-open condition on `A`.

Combined with the fact that a continuous surjection from a compact space to a Hausdorff space is a
quotient map, this identifies mapping spaces out of a quotient such as `I^n / ∂I^n ≅ S^n` with
subspaces of mapping spaces out of the cube.

## Main declarations

* `ContinuousMap.isInducing_precomp_of_surjective`: precomposition with a continuous surjection
  `q : A → B` from a compact space to a Hausdorff space is inducing, on the compact-open
  topologies.
* `ContinuousMap.isEmbedding_precomp_of_surjective`: the same, as an embedding.
* `ContinuousMap.homeomorphFactorsThrough`, with `homeomorphFactorsThrough_apply` and
  `homeomorphFactorsThrough_symm_apply_comp`: for such a `q`, `C(B, X)` is homeomorphic to the
  subspace of maps `A → X` that are constant on the fibres of `q`.
-/

public section

open Set Topology

namespace ContinuousMap

variable {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]

/-- Precomposition with a continuous surjection `q` from a compact space is inducing for the
compact-open topologies. -/
theorem isInducing_precomp_of_surjective [CompactSpace A] [T2Space B] (q : C(A, B))
    (hq : Function.Surjective q) :
    IsInducing (fun f : C(B, X) => f.comp q) := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp (continuous_precomp q)) ?_⟩
  refine le_generateFrom ?_
  rintro _ ⟨K, hK, U, hU, rfl⟩
  have hpre : IsOpen {g : C(A, X) | MapsTo g (q ⁻¹' K) U} :=
    isOpen_setOfPred_mapsTo ((hK.isClosed.preimage q.continuous).isCompact) hU
  refine ⟨_, hpre, ?_⟩
  ext f
  constructor
  · intro h b hb
    obtain ⟨a, rfl⟩ := hq b
    exact h hb
  · intro h a ha
    exact h ha

/-- Precomposition with a continuous surjection `q` from a compact space is an embedding. -/
theorem isEmbedding_precomp_of_surjective [CompactSpace A] [T2Space B] (q : C(A, B))
    (hq : Function.Surjective q) :
    IsEmbedding (fun f : C(B, X) => f.comp q) :=
  ⟨isInducing_precomp_of_surjective q hq, fun _ _ h => (cancel_right hq).1 h⟩

/-- Maps out of a Hausdorff quotient `B` of a compact space `A` are the maps out of `A` that are
constant on the fibres of the quotient map `q`: precomposition with `q` is a homeomorphism from
`C(B, X)` onto the subspace of such maps. -/
noncomputable def homeomorphFactorsThrough [CompactSpace A] [T2Space B] (q : C(A, B))
    (hq : Function.Surjective q) :
    C(B, X) ≃ₜ {g : C(A, X) // Function.FactorsThrough g q} :=
  (isEmbedding_precomp_of_surjective q hq).toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext g
      refine ⟨?_, fun hg => ?_⟩
      · rintro ⟨f, rfl⟩ a b h
        exact congrArg f h
      · have hqm : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous hq
        exact ⟨hqm.lift g hg, hqm.lift_comp g hg⟩))

@[simp]
theorem homeomorphFactorsThrough_apply [CompactSpace A] [T2Space B] (q : C(A, B))
    (hq : Function.Surjective q) (f : C(B, X)) :
    (homeomorphFactorsThrough q hq f : C(A, X)) = f.comp q := by
  rw [homeomorphFactorsThrough]
  rfl

/-- The inverse of `homeomorphFactorsThrough` evaluates, at the image under `q` of a point, to the
value at that point of the map out of the source. -/
theorem homeomorphFactorsThrough_symm_apply_comp [CompactSpace A] [T2Space B] (q : C(A, B))
    (hq : Function.Surjective q) (g : {g : C(A, X) // Function.FactorsThrough g q}) (a : A) :
    (homeomorphFactorsThrough q hq).symm g (q a) = g.1 a := by
  have h := congrArg (fun f : {g : C(A, X) // Function.FactorsThrough g q} => f.1 a)
    ((homeomorphFactorsThrough q hq).apply_symm_apply g)
  rwa [homeomorphFactorsThrough_apply] at h

end ContinuousMap
