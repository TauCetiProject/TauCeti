/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# Examples for the canonical adic topology on affine formal opens

We test `TauCeti.FormalScheme.sectionsTopology`, `TauCeti.FormalScheme.IsAffineOpen.Sections`, and
the affine reconstruction isomorphism `TauCeti.FormalScheme.IsAffineOpen.isoSpf` (EGA I, Ch. I,
10.4.2) on concrete formal schemes:

1. **`p`-adic formal disc (`ofSpf ℤ_[p]`):** the topologized section ring
   `(isAffineOpen_top_ofSpf ℤ_[p]).Sections` is an `IsAdicRing` whose topology is **not** discrete
   (even though the underlying topological space has a single point), `isoSpf` reconstructs
   `(ofSpf ℤ_[p]).restrict ⊤` from its topologized sections, and `ofSpf ℤ_[p]` is not isomorphic to
   `ofScheme.obj Y` for any scheme `Y`.
2. **Nonreduced ordinary scheme (`Spec (ZMod 4)`):** on `ofScheme.obj (Spec (ZMod 4))`,
   `sectionsTopology` is `⊥` (discrete) while the section ring remains nonreduced (`2 ≠ 0` and
   `2 ^ 2 = 0`), distinguishing nilpotents from formal directions.
3. **Empty open and zero coordinate ring (`ZMod 1`):** `sectionsTopology` on `⊥` (and on
   `ofSpf (ZMod 1)`) is `⊥` with no nontriviality assumption.
-/

public section

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry TauCeti
open TauCeti.FormalScheme

noncomputable section

namespace TauCeti.Examples.FormalScheme.SectionsTopology

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance padicIntIsAdicRing : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    by rw [PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

private theorem not_discreteTopology_padicInt : ¬ DiscreteTopology ℤ_[p] := by
  intro hdisc
  have hnil : Filter.Tendsto (fun n : ℕ ↦ (p : ℤ_[p]) ^ n) Filter.atTop (𝓝 0) :=
    (Huber.PadicInt.isTopologicallyNilpotent_iff_dvd (c := (p : ℤ_[p]))).mpr dvd_rfl
  rw [nhds_discrete, Filter.tendsto_pure] at hnil
  obtain ⟨n, hn⟩ := hnil.exists
  exact pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hn

-- Over `ofSpf ℤ_[p]`, the topologized section ring `hU.Sections` is a nondiscrete adic ring and
-- canonically reconstructs `(ofSpf ℤ_[p]).restrict ⊤` via `hU.isoSpf` (EGA I, Ch. I, 10.4.2).
example :
    let hU : (ofSpf ℤ_[p]).IsAffineOpen ⊤ := isAffineOpen_top_ofSpf ℤ_[p]
    IsAdicRing hU.Sections ∧ ¬ DiscreteTopology hU.Sections ∧
      Nonempty ((ofSpf ℤ_[p]).restrict ⊤ ≅ ofSpf hU.Sections) := by
  intro hU
  refine ⟨inferInstance, fun hdisc ↦ ?_, ⟨hU.isoSpf⟩⟩
  let e : ofSpf ℤ_[p] ≅ (Spec (CommRingCat.of hU.Sections)).toFormalScheme :=
    (ofSpf ℤ_[p]).restrictTopIso.symm ≪≫ hU.isoSpf ≪≫ (ofSchemeSpecIso hU.Sections).symm
  exact not_discreteTopology_padicInt p (discreteTopology_of_iso_toFormalScheme e)

-- `ofSpf ℤ_[p]` is a genuine formal scheme: it is not isomorphic to `ofScheme.obj Y` for any
-- ordinary scheme `Y`.
example : ¬ ∃ Y : Scheme.{0}, Nonempty (ofSpf ℤ_[p] ≅ ofScheme.obj Y) := by
  simp only [ofScheme_obj, exists_iso_toFormalScheme_iff]
  exact not_discreteTopology_padicInt p

end Padic

section DiscreteAndNonreduced

/-- The discrete topology on `ZMod n` for the finite-ring checks. -/
local instance zmodTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance zmodDiscreteTopology (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

-- On `ofScheme.obj (Spec (ZMod 4))`, the section topology on `⊤` is discrete (`⊥`), yet the
-- topologized section ring is nonreduced.
example :
    let Y := Spec (CommRingCat.of (ZMod 4))
    let hU : Y.toFormalScheme.IsAffineOpen ⊤ :=
      (isAffineOpen_toFormalScheme_iff Y ⊤).mpr (isAffineOpen_top Y)
    DiscreteTopology hU.Sections ∧ ¬ IsReduced hU.Sections := by
  intro Y hU
  refine ⟨inferInstance, fun hred ↦ ?_⟩
  let e : ZMod 4 ≃+* hU.Sections :=
    (asIso (toSpecΓ (CommRingCat.of (ZMod 4)))).commRingCatIsoToRingEquiv.trans
      hU.sectionsRingEquiv.symm
  have h2_sq : (e (2 : ZMod 4)) ^ 2 = 0 := by
    rw [← map_pow, show (2 : ZMod 4) ^ 2 = 0 by decide, map_zero]
  have h2_zero : e (2 : ZMod 4) = 0 := eq_zero_of_pow_eq_zero h2_sq
  exact (by decide : (2 : ZMod 4) ≠ 0) (e.injective (h2_zero.trans (map_zero e).symm))

-- Empty formal opens and the zero coordinate ring `ZMod 1` carry the `⊥` section topology.
example (X : FormalScheme) (hbot : X.IsAffineOpen ⊥) : X.sectionsTopology ⊥ hbot = ⊥ :=
  X.sectionsTopology_bot hbot

example : (ofSpf (ZMod 1)).sectionsTopology ⊤ (isAffineOpen_top_ofSpf (ZMod 1)) = ⊥ := by
  let := (ofSpf (ZMod 1)).sectionsTopology ⊤ (isAffineOpen_top_ofSpf (ZMod 1))
  have : Subsingleton ((ofSpf (ZMod 1)).presheaf.obj (op ⊤)) :=
    (ofSpfGlobalSectionsIso (ZMod 1)).commRingCatIsoToRingEquiv.subsingleton
  exact Subsingleton.elim _ _

end DiscreteAndNonreduced

end TauCeti.Examples.FormalScheme.SectionsTopology
