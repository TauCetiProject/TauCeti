/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Projectivization.Plucker
public import TauCeti.Topology.Algebra.Plucker
public import TauCeti.Topology.Algebra.Projectivization
public import TauCeti.Topology.Grassmannian.Basic

import TauCeti.Algebra.Module.Submodule.Map

/-!
# The continuous Plücker map of a finite Grassmannian

The Plücker point of an `r`-plane in `𝕜^N` lies in projective space with coordinates
indexed by the `r`-element subsets of `Fin N`. The fixed-rank map `pluckerMap` is
continuous for the frame-quotient topology and injective. Consequently the finite
real and complex Grassmannians are Hausdorff, including the empty and extreme-rank
cases. No compactness or choice of orthonormal frames is needed.

The algebraic input is `TauCeti.mk_plucker_eq_mk_plucker_iff`: proportional maximal
minors characterize equality of spans. The topology on the target is the native
projective quotient topology developed in `TauCeti.Topology.Algebra.Projectivization`.

The construction follows Milnor–Stasheff, *Characteristic Classes*, §5.
-/

public section

open Set Topology

namespace TauCeti.finiteGrassmannian

variable {𝕜 : Type*} [Field 𝕜] {r N : ℕ}

/-- The existing `Submodule.relativePluckerPoint`, transported to the projective
coordinate space indexed by `r` rather than by the subspace's dimension. -/
noncomputable def pluckerMap (V : finiteGrassmannian 𝕜 r N) :
    Projectivization 𝕜 (Set.powersetCard (Fin N) r → 𝕜) :=
  cast (congrArg (fun n ↦ Projectivization 𝕜 (Set.powersetCard (Fin N) n → 𝕜)) V.2)
    V.1.relativePluckerPoint

/-- The fixed-rank Plücker map is computed by the maximal minors of any basis. -/
theorem pluckerMap_eq_mk (V : finiteGrassmannian 𝕜 r N) (b : Module.Basis (Fin r) 𝕜 V.1) :
    pluckerMap V = Projectivization.mk 𝕜 (plucker fun i ↦ (b i : Fin N → 𝕜))
      ((plucker_ne_zero_iff _).2 b.linearIndependent_coe_basis) := by
  rcases V with ⟨V, hV⟩
  subst r
  exact Submodule.relativePluckerPoint_eq_mk b

/-- The Plücker map is computed by the maximal minors of any spanning frame. -/
@[simp]
theorem pluckerMap_frameSpan (f : finiteFullRankFrame 𝕜 r N) :
    pluckerMap (frameSpan f) =
      Projectivization.mk 𝕜 (plucker f.1) ((plucker_ne_zero_iff _).2 f.2) := by
  let b := Module.finBasisOfFinrankEq 𝕜 (frameSpan f).1 (frameSpan f).2
  rw [pluckerMap_eq_mk _ b]
  apply (mk_plucker_eq_mk_plucker_iff b.linearIndependent_coe_basis f.2).2
  simpa only [LinearMap.id_apply, Submodule.map_id, coe_frameSpan] using
    (Submodule.map_eq_span_basis (frameSpan f).1 b LinearMap.id).symm

/-- The Plücker point determines the subspace. -/
theorem pluckerMap_injective :
    Function.Injective (pluckerMap (𝕜 := 𝕜) (r := r) (N := N)) := by
  intro V W h
  obtain ⟨f, rfl⟩ := frameSpan_surjective V
  obtain ⟨g, rfl⟩ := frameSpan_surjective W
  apply Subtype.ext
  simp only [coe_frameSpan]
  exact (mk_plucker_eq_mk_plucker_iff f.2 g.2).1 (by simpa only [pluckerMap_frameSpan] using h)

variable [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/-- The fixed-rank Plücker map is continuous for the quotient topology on the
Grassmannian and the quotient topology on projective space. -/
@[fun_prop]
theorem continuous_pluckerMap :
    Continuous (pluckerMap (𝕜 := 𝕜) (r := r) (N := N)) := by
  apply isQuotientMap_frameSpan.continuous_iff.2
  simpa only [Function.comp_def, pluckerMap_frameSpan] using
    Projectivization.continuous_mk
      (continuous_plucker.comp (continuous_subtype_val :
        Continuous fun f : finiteFullRankFrame 𝕜 r N ↦ f.1))
      (fun f ↦ (plucker_ne_zero_iff _).2 f.2)

/-- Finite Grassmannians over Hausdorff topological fields are Hausdorff.
In particular, this applies over the real and complex numbers. -/
instance [T2Space 𝕜] : T2Space (finiteGrassmannian 𝕜 r N) := by
  let : SeparatingDual 𝕜 (Set.powersetCard (Fin N) r → 𝕜) := ⟨fun x hx ↦ by
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hx
    exact ⟨ContinuousLinearMap.proj s, hs⟩⟩
  exact T2Space.of_injective_continuous pluckerMap_injective continuous_pluckerMap

end TauCeti.finiteGrassmannian
