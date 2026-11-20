/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothSingular.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Integral cycles of smooth singular chains

The smooth singular `k`-chains of a manifold `M` with integer coefficients form the degree-`k` term
of the chain complex of the simplicial set `TauCeti.smoothSingularSubcomplex I M` with coefficients
in `ℤ`. This file names its cycles, `TauCeti.smoothIntCycles I M k`, as an additive subgroup of the
chains; the boundary of a `(k + 1)`-chain as a `k`-cycle, `TauCeti.smoothIntBoundary I M k`; and the
pushforward of cycles along a smooth map, `TauCeti.smoothIntCyclesMap`, which commutes with
boundaries. Homomorphisms out of these cycles are the differential characters of Cheeger and
Simons.
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type) [TopologicalSpace M] [ChartedSpace H M]

section Cycles

/-- The smooth singular integral `k`-cycles of `M`: the smooth singular `k`-chains with integer
coefficients whose boundary vanishes. Every `0`-chain is a cycle. -/
def smoothIntCycles (k : ℕ) :
    AddSubgroup (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X k) :=
  (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d k
    (k - 1)).hom.toAddMonoidHom.ker

variable {I M} in
/-- A chain is a cycle exactly when its boundary vanishes. -/
theorem mem_smoothIntCycles_iff {k : ℕ}
    {c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X k} :
    c ∈ smoothIntCycles I M k ↔
      (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d k
        (k - 1)).hom c = 0 :=
  AddMonoidHom.mem_ker

/-- The boundary of a smooth singular integral `(k + 1)`-chain, as a `k`-cycle. -/
def smoothIntBoundary (k : ℕ) :
    ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1) →+
      smoothIntCycles I M k :=
  AddMonoidHom.codRestrict
    (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1)
      k).hom.toAddMonoidHom _
    fun c ↦ mem_smoothIntCycles_iff.mpr <| by
      rw [LinearMap.toAddMonoidHom_coe, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
        HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The cycle `smoothIntBoundary I M k c` is the boundary of `c`. -/
@[simp]
theorem coe_smoothIntBoundary (k : ℕ)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1)) :
    (smoothIntBoundary I M k c :
      ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X k) =
      (((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).d (k + 1) k).hom
        c :=
  (rfl)

section Map

variable {I M} {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N}

/-- The map of smooth singular integral `k`-cycles induced by a smooth map `f`: pushforward of
chains along `f`. -/
def smoothIntCyclesMap (hf : ContMDiff I J ∞ f) (k : ℕ) :
    smoothIntCycles I M k →+ smoothIntCycles J N k :=
  AddMonoidHom.codRestrict
    ((((SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)).f
      k).hom.toAddMonoidHom).comp (smoothIntCycles I M k).subtype) _
    fun z ↦ mem_smoothIntCycles_iff.mpr <| by
      rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, ← LinearMap.comp_apply,
        ← ModuleCat.hom_comp, HomologicalComplex.Hom.comm, ModuleCat.hom_comp,
        LinearMap.comp_apply, AddSubgroup.coe_subtype, mem_smoothIntCycles_iff.mp z.2, map_zero]

/-- The pushforward of a cycle is the pushforward of the underlying chain. -/
@[simp]
theorem coe_smoothIntCyclesMap (hf : ContMDiff I J ∞ f) (k : ℕ) (z : smoothIntCycles I M k) :
    (smoothIntCyclesMap hf k z :
      ((smoothSingularSubcomplex J N : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X k) =
      ((SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)).f k).hom z :=
  (rfl)

/-- Pushforward along a smooth map commutes with taking boundaries. -/
theorem smoothIntCyclesMap_smoothIntBoundary (hf : ContMDiff I J ∞ f) (k : ℕ)
    (c : ((smoothSingularSubcomplex I M : SSet).chainComplex (ModuleCat.of ℤ ℤ)).X (k + 1)) :
    smoothIntCyclesMap hf k (smoothIntBoundary I M k c) = smoothIntBoundary J N k
      (((SSet.chainComplexMap (smoothSingularSubcomplexMap f hf) (ModuleCat.of ℤ ℤ)).f
        (k + 1)).hom c) := by
  ext1
  rw [coe_smoothIntCyclesMap, coe_smoothIntBoundary, coe_smoothIntBoundary, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, ← HomologicalComplex.Hom.comm, ModuleCat.hom_comp, LinearMap.comp_apply]

end Map

end Cycles

end TauCeti
