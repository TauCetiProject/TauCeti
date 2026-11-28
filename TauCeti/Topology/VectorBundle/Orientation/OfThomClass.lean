/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# Integral Thom classes come from orientations

Let `E → B` be a real vector bundle with model fibre `F` of dimension `n + 1`. Every orientation
`o` of `E` has an integral Thom class `U ∈ Hⁿ⁺¹(E, E₀; ℤ)`
(`TauCeti.VectorBundleOrientation.thomClass`), restricting on every fibre to the generator selected
by the fibre orientation. This file proves the converse over a locally path-connected base, such
as a manifold: **every integral Thom class is the Thom class of an orientation**
(`TauCeti.exists_vectorBundleOrientation_thomClass_eq`). So a bundle with an integral Thom class
is orientable (`TauCeti.IsThomClass.nonempty_vectorBundleOrientation`), and a real vector bundle
over a locally path-connected base is orientable exactly when it has an integral Thom class
(`TauCeti.nonempty_vectorBundleOrientation_iff_exists_isThomClass`). This is the integral part of
the equivalence between orientations and Thom classes of Milnor and Stasheff (§9 and Theorem
10.4): with coefficients in a ring in which `2 = 0` every bundle has a Thom class
(`TauCeti.exists_isThomClass_of_two_eq_zero`), so integral coefficients are needed.

The proof reads a class `u` with generating fibre restrictions in local trivializations.

* On the fibre over `b`, read through a linear trivialization `e` at `b`, the restriction of `u`
  generates `Hⁿ⁺¹(F, F ∖ {0}; ℤ) ≅ ℤ`, so it is the generator selected by one of the two
  orientations of `F` (`Orientation.exists_eq_localCohomologyClass`). Carried back to the fibre
  by `e`, this orientation is an orientation of `E_b` which does not depend on `e`
  (`Orientation.singularCohomologyMap_localCohomologyClass_map_eq`).
* Over points joined by a path in the base set of `e`, the fibre inclusions read through `e` are
  homotopic, so they induce the same map on homology
  (in `Bundle.Trivialization`,
  `singularHomologyMap_complZeroPairIso_inv_comp_fiberThomPairOverMap_eq_of_joinedIn`), and the
  readings of `u` pair in the same way with every local orientation of `F`. A class of
  `Hⁿ⁺¹(F, F ∖ {0}; ℤ)` is determined by this pairing (`Orientation.localCohomology_ext`), so the
  reading of `u` is constant along paths in the base set (in `Bundle.Trivialization`,
  `singularCohomologyMap_complZeroPairIso_inv_comp_fiberThomPairMap_eq_of_joinedIn`).
* Over a locally path-connected base, the points of the base set joined to `b` within it form a
  neighbourhood of `b`, so the fibre orientations are locally constant in the trivialization at
  `b`: they form an orientation of `E`, and `u` is its Thom class by the characterization of
  Thom classes through their fibre restrictions
  (`TauCeti.VectorBundleOrientation.eq_thomClass_iff`).

The hypothesis on the base cannot be dropped: singular cohomology only sees path components, and
over the compact set `{0} ∪ {1 / (k + 1) | k : ℕ}` of the real line, whose points are its path
components, the fibre restrictions of a class of the trivial line bundle can be prescribed
independently at every point, `1` at the points `1 / (k + 1)` and `-1` at `0`. That class has
generating fibre restrictions, but the fibre orientations it selects are not locally constant
at `0`.

## Main results

* `singularCohomologyMap_complZeroPairIso_inv_comp_fiberThomPairMap_eq_of_joinedIn`, in
  `Bundle.Trivialization`: a class of `Hⁿ⁺¹(E, E₀; ℤ)` read on the fibres through a linear
  trivialization is the same over points joined by a path in its base set.
* `TauCeti.exists_vectorBundleOrientation_thomClass_eq`: over a locally path-connected base, a
  class of `Hⁿ⁺¹(E, E₀; ℤ)` restricting to generators on all fibres is the Thom class of an
  orientation.
* `TauCeti.IsThomClass.nonempty_vectorBundleOrientation`: a bundle with an integral Thom class
  over a locally path-connected base is orientable.
* `TauCeti.nonempty_vectorBundleOrientation_iff_exists_isThomClass`: over a locally
  path-connected base, a bundle is orientable exactly when it has an integral Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (orientations as compatible fibre generators) and Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, the definition of an orientation of a vector
  bundle preceding Theorem 4D.10.
-/

public section

noncomputable section

open Bundle CategoryTheory Module Set Topology

universe w

section JoinedIn

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] {n : ℕ}
  (hF : finrank ℝ F = n + 1)

namespace Bundle.Trivialization

open TauCeti

include hF in
/-- **Fibre classes read in a trivialization are constant along paths in its base set.** Let
`u ∈ Hⁿ⁺¹(E, E₀; ℤ)` and let `b` and `b'` be joined by a path in the base set of a linear
trivialization `e`. Then the restrictions of `u` to the fibres over `b` and `b'`, read through `e`
as classes of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)`, are equal. -/
theorem singularCohomologyMap_complZeroPairIso_inv_comp_fiberThomPairMap_eq_of_joinedIn
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b b' : B} (h : JoinedIn e.baseSet b b')
    (u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) :
    TopPair.singularCohomologyMap
        ((e.continuousLinearEquivAt ℝ b h.source_mem).complZeroPairIso.inv ≫
          fiberThomPairMap F E b) (n + 1) u =
      TopPair.singularCohomologyMap
        ((e.continuousLinearEquivAt ℝ b' h.target_mem).complZeroPairIso.inv ≫
          fiberThomPairMap F E b') (n + 1) u := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  -- The two fibre inclusions, read through `e`, induce the same map on homology.
  have hhom : TopPair.singularHomologyMap
        ((e.continuousLinearEquivAt ℝ b h.source_mem).complZeroPairIso.inv ≫
          fiberThomPairMap F E b) (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) =
      TopPair.singularHomologyMap
        ((e.continuousLinearEquivAt ℝ b' h.target_mem).complZeroPairIso.inv ≫
          fiberThomPairMap F E b') (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) := by
    have h' : JoinedIn (univ ∩ e.baseSet) b b' := by rwa [univ_inter]
    have hj := congrArg (· ≫ TopPair.singularHomologyMap (thomPairOverUnivIso F E).hom
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))
      (e.singularHomologyMap_complZeroPairIso_inv_comp_fiberThomPairOverMap_eq_of_joinedIn _ h'
        (n + 1) hF)
    simpa only [← TopPair.singularHomologyMap_comp, Category.assoc,
      fiberThomPairOverMap_comp_thomPairOverUnivIso_hom] using hj
  -- So the two readings pair in the same way with every local orientation of `F`.
  let ω : Orientation ℝ F (Fin (n + 1)) := (Module.finBasisOfFinrankEq ℝ F hF).orientation
  refine ω.localCohomology_ext hF ?_
  rw [TopPair.singularKronecker_naturality, TopPair.singularKronecker_naturality, ← hhom]

end Bundle.Trivialization

end JoinedIn

namespace TauCeti

section ThomClass

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ} (hF : finrank ℝ F = n + 1)

include hF in
/-- **A generator of the integral cohomology of a fibre is selected by a fibre orientation.** If
the restriction of `u ∈ Hⁿ⁺¹(E, E₀; ℤ)` to the fibre pair over `b` generates
`Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)`, then it is the generator selected by an orientation `θ` of `E_b`: every
linear trivialization at `b` reads it as the generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected by `θ`
read in that trivialization. -/
theorem exists_orientation_singularCohomologyMap_fiberThomPairMap_eq
    (u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) (b : B)
    (hu : Submodule.span ℤ {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (n + 1) u} =
      ⊤) :
    ∃ θ : Orientation ℝ (E b) (Fin (n + 1)), ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ]
      (hb : b ∈ e.baseSet), TopPair.singularCohomologyMap (fiberThomPairMap F E b) (n + 1) u =
        TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
          (n + 1) ((e.mapOrientation (Fin (n + 1)) hb θ).localCohomologyClass hF) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  let L := ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb).complZeroPairIso
  -- Read in the trivialization at `b`, the fibre class generates, since an isomorphism of pairs
  -- induces a linear isomorphism in cohomology; so it is selected by an orientation `ω` of `F`.
  obtain ⟨ω, hω⟩ := Orientation.exists_eq_localCohomologyClass hF
    (((TopPair.singularCohomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).mapIso L.symm.op
      ).toLinearEquiv.span_singleton_apply_eq_top_iff.2 hu)
  set θ := ((trivializationAt F E b).mapOrientation (Fin (n + 1)) hb).symm ω
  refine ⟨θ, fun e _ hb' ↦ ?_⟩
  -- Any other linear trivialization reads the orientation `θ` of the fibre in the same way.
  have key : TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom
      (n + 1) ((e.mapOrientation (Fin (n + 1)) hb' θ).localCohomologyClass hF) =
        TopPair.singularCohomologyMap L.hom (n + 1) (ω.localCohomologyClass hF) := by
    rw [← Equiv.apply_symm_apply ((trivializationAt F E b).mapOrientation (Fin (n + 1)) hb) ω,
      Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply]
    exact Orientation.singularCohomologyMap_localCohomologyClass_map_eq θ _ _ hF hF
  rw [key, ← hω]
  exact (Iso.hom_inv_id_apply ((TopPair.singularCohomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ))
    ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).mapIso L.symm.op) _).symm

variable [LocallyPathConnectedSpace B]

include hF in
/-- **An integral Thom class is the Thom class of an orientation.** Over a locally path-connected
base, a class `u ∈ Hⁿ⁺¹(E, E₀; ℤ)` whose restriction to the fibre pair over every point generates
`Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)` is the Thom class of an orientation of `E`: the orientation of each fibre
is the one selecting the restriction of `u` to it. -/
theorem exists_vectorBundleOrientation_thomClass_eq
    (u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1))
    (hu : ∀ b, Submodule.span ℤ {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (n + 1) u} =
      ⊤) :
    ∃ o : VectorBundleOrientation F E (Fin (n + 1)), o.thomClass hF = u := by
  -- The orientation `θ b` of the fibre over `b` selects the restriction of `u` to it.
  choose θ hθe using fun b ↦ exists_orientation_singularCohomologyMap_fiberThomPairMap_eq hF u b
    (hu b)
  have hread (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet) :
      TopPair.singularCohomologyMap ((e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv ≫
          fiberThomPairMap F E b) (n + 1) u =
        (e.mapOrientation (Fin (n + 1)) hb (θ b)).localCohomologyClass hF := by
    rw [TopPair.singularCohomologyMap_comp_apply, hθe b e hb,
      ← TopPair.singularCohomologyMap_comp_apply]
    simp
  -- The fibre orientations are locally constant in the trivialization at each point: near `b`
  -- every point is joined to `b` by a path in its base set, along which the reading of `u` is
  -- constant.
  obtain ⟨o, ho⟩ : ∃ o : VectorBundleOrientation F E (Fin (n + 1)), ⇑o = θ :=
    ⟨VectorBundleOrientation.ofEventually (by rw [Fintype.card_fin, hF]) θ
      (fun b ↦ trivializationAt F E b) (fun b ↦ FiberBundle.mem_baseSet_trivializationAt' b)
      fun b ↦ by
        have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
        filter_upwards [pathComponentIn_mem_nhds
          ((trivializationAt F E b).open_baseSet.mem_nhds hb)] with x hx hx'
        apply Orientation.localCohomologyClass_injective hF
        simp only
        rw [← hread _ x hx']
        let e := trivializationAt F E b
        exact (e.singularCohomologyMap_complZeroPairIso_inv_comp_fiberThomPairMap_eq_of_joinedIn hF
          hx u).symm.trans (hread _ b hb),
      VectorBundleOrientation.coe_ofEventually _ _ _ _ _⟩
  -- The fibre orientations of `o` are the `θ b`, so `u` restricts to the generators of `o`.
  exact ⟨o, ((VectorBundleOrientation.eq_thomClass_iff o hF u).2 fun e _ b hb ↦
    (hθe b e hb).trans (by rw [ho])).symm⟩

include hF in
/-- **A bundle with an integral Thom class is orientable**, over a locally path-connected base. -/
theorem IsThomClass.nonempty_vectorBundleOrientation
    {u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F)}
    (hu : IsThomClass F E u) : Nonempty (VectorBundleOrientation F E (Fin (n + 1))) := by
  -- Transport along `finrank ℝ F = n + 1` commutes with the fibre restrictions.
  have key {d : ℕ} (hd : finrank ℝ F = d) (b : B) : Submodule.span ℤ
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) d (hd ▸ u)} = ⊤ := by
    subst hd
    exact (isThomClass_iff.1 hu).2 b
  obtain ⟨o, -⟩ := exists_vectorBundleOrientation_thomClass_eq hF _ (key hF)
  exact ⟨o⟩

include hF in
/-- **Orientations and integral Thom classes.** Over a locally path-connected base, a real vector
bundle of positive rank is orientable exactly when it has an integral Thom class. -/
theorem nonempty_vectorBundleOrientation_iff_exists_isThomClass :
    Nonempty (VectorBundleOrientation F E (Fin (n + 1))) ↔
      ∃ u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F), IsThomClass F E u :=
  ⟨fun ⟨o⟩ ↦ ⟨_, o.isThomClass_thomClass hF⟩,
    fun ⟨_, hu⟩ ↦ hu.nonempty_vectorBundleOrientation hF⟩

end ThomClass

end TauCeti
