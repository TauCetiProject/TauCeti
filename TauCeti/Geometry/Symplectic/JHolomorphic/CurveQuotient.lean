/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.IsLocalHomeomorph
public import TauCeti.Geometry.Symplectic.JHolomorphic.BranchDegree
import TauCeti.Geometry.Manifold.MFDeriv.LocalInjectivity

/-!
# The quotient of a closed pseudoholomorphic curve by its coincident branches

Let `S` be a compact connected Hausdorff Riemann surface, `N` a Hausdorff manifold with a smooth
almost complex structure `J`, and `u : S → N` a nonconstant pseudoholomorphic map of class `C²`,
with the finite preimage `B = u⁻¹(u(Crit u))` of its critical values. The closure `Γ` in `S × S` of
the coincident-branch relation (`TauCeti.coincidentBranchClosure`) is an equivalence relation with
finite classes (`TauCeti.equivalence_coincidentBranchClosure`). In McDuff–Salamon's construction of
the simple curve underlying `u` (Proposition 2.5.1), `u` factors as `u = v ∘ π` through the quotient
map `π : S → S / Γ`, which is a branched cover of degree `d`, the number of coincident branches at a
point off `B`, with local degree `e_z` at `z`, the local multiplicity
`TauCeti.coincidentBranchMultiplicity`.

This file constructs the quotient `S / Γ` (`TauCeti.CoincidentBranchQuotient`), with the quotient
map `π` (`TauCeti.CoincidentBranchQuotient.mk`), and establishes this topological skeleton of the
construction:

* `S / Γ` is a compact connected Hausdorff space
  (`TauCeti.CoincidentBranchQuotient.t2Space`), and two points have the same image under `π`
  exactly when they are related by `Γ` (`TauCeti.CoincidentBranchQuotient.mk_eq_mk_iff`);
* `π` is an open quotient map (`TauCeti.CoincidentBranchQuotient.isOpenQuotientMap_mk`) and a
  closed map with finite fibres;
* `u` descends to a continuous map `v : S / Γ → N` with `u = v ∘ π`
  (`TauCeti.CoincidentBranchQuotient.lift`, `TauCeti.CoincidentBranchQuotient.lift_comp_mk`);
* `B` is a union of fibres of `π`, `π` is a local homeomorphism on `S \ B`
  (`TauCeti.CoincidentBranchQuotient.isLocalHomeomorphOn_mk`), and `π` is a covering map over the
  complement of the finite set `π(B)` (`TauCeti.CoincidentBranchQuotient.isCoveringMapOn_mk`)
  whose fibres all have the same number `d ≥ 1` of points
  (`TauCeti.CoincidentBranchQuotient.exists_pos_forall_ncard_preimage_mk_eq`);
* near `z`, the points of `S / Γ` outside `π(B)` near `π z` have exactly `e_z` preimages near `z`
  (`TauCeti.CoincidentBranchQuotient.exists_mem_nhds_forall_eventually_ncard_inter_preimage_mk_eq`),
  so `e_z` is the local degree of `π` at `z`.

Openness of `π` is where the analysis enters: the saturation of an open set `W` is open because
`Γ` propagates to nearby points
(`TauCeti.eventually_exists_germFactorsThrough_of_mem_coincidentBranchClosure`). If `a ∈ W` is
related to `z`, every point near `z` off the finite set `B` has a coincident branch at a point of
`W`. Hausdorffness then follows from openness and the closedness of `Γ`. Near a point
`z ∉ B` the map `u` is immersed, hence injective, and related points have the same image under `u`,
so `π` is injective near `z`.

The holomorphic charts on `S / Γ`, which make it a Riemann surface and `π` and `v` holomorphic and
pseudoholomorphic, are not constructed here.

## Main definitions

* `TauCeti.CoincidentBranchQuotient`: the quotient `S / Γ` of `S` by the closure `Γ` of the
  coincident-branch relation of `u`.
* `TauCeti.CoincidentBranchQuotient.mk`: the quotient map `π : S → S / Γ`.
* `TauCeti.CoincidentBranchQuotient.lift`: the map `v : S / Γ → N` with `u = v ∘ π`.

## Main results

* `TauCeti.CoincidentBranchQuotient.mk_eq_mk_iff`,
  `TauCeti.CoincidentBranchQuotient.mk_eq_mk_iff_of_notMem`: the fibres of `π` are the classes of
  `Γ`, and off `B` the classes of the coincident-branch relation.
* `TauCeti.CoincidentBranchQuotient.isOpenMap_mk`,
  `TauCeti.CoincidentBranchQuotient.isOpenQuotientMap_mk`: `π` is an open quotient map.
* `TauCeti.CoincidentBranchQuotient.t2Space`: `S / Γ` is Hausdorff.
* `TauCeti.CoincidentBranchQuotient.isClosedMap_mk`,
  `TauCeti.CoincidentBranchQuotient.finite_preimage_mk`: `π` is closed with finite fibres.
* `TauCeti.CoincidentBranchQuotient.continuous_lift`,
  `TauCeti.CoincidentBranchQuotient.lift_comp_mk`: `u` descends to a continuous map on `S / Γ`.
* `TauCeti.CoincidentBranchQuotient.preimage_image_mk_criticalValuePreimage`: `B` is saturated.
* `TauCeti.CoincidentBranchQuotient.isLocalHomeomorphOn_mk`: `π` is a local homeomorphism off `B`.
* `TauCeti.CoincidentBranchQuotient.isCoveringMapOn_mk`: `π` is a covering map over the
  complement of `π(B)`.
* `TauCeti.CoincidentBranchQuotient.exists_pos_forall_ncard_preimage_mk_eq`: off `π(B)` the fibres
  of `π` all have `d ≥ 1` points.
* `TauCeti.CoincidentBranchQuotient.exists_mem_nhds_forall_eventually_ncard_inter_preimage_mk_eq`:
  the local degree of `π` at `z` is `e_z`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition 2.5.1 and its proof.
* C. Wendl, *Lectures on holomorphic curves in symplectic and contact geometry*, arXiv:1011.1690,
  Proposition 4.3.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure RiemannSurface

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {J : SmoothAlmostComplexStructure I N} {u : S → N}

variable (I u) in
/-- **The quotient `S / Γ` of a Riemann surface by the coincident branches of `u : S → N`**: the
quotient of `S` by the closure `Γ` in `S × S` of the coincident-branch relation of `u`
(`TauCeti.coincidentBranchClosure`), with the quotient topology. For a nonconstant `C²`
pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff almost
complex manifold, `Γ` is an equivalence relation, `S / Γ` is a compact connected Hausdorff space
(`TauCeti.CoincidentBranchQuotient.t2Space`), and `u` factors through it
(`TauCeti.CoincidentBranchQuotient.lift_comp_mk`). -/
@[expose]
def CoincidentBranchQuotient : Type _ :=
  Quot fun z ζ : S ↦ (z, ζ) ∈ coincidentBranchClosure I u

namespace CoincidentBranchQuotient

instance : TopologicalSpace (CoincidentBranchQuotient I u) :=
  inferInstanceAs (TopologicalSpace (Quot _))

variable (I u) in
/-- **The quotient map** `π : S → S / Γ` onto the quotient by the closure `Γ` of the
coincident-branch relation of `u`. -/
@[expose]
def mk : S → CoincidentBranchQuotient I u :=
  Quot.mk _

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- Points related by the closure `Γ` of the coincident-branch relation have the same image in
`S / Γ`. -/
theorem mk_eq_mk_of_mem_coincidentBranchClosure {z ζ : S}
    (h : (z, ζ) ∈ coincidentBranchClosure I u) : mk I u z = mk I u ζ :=
  Quot.sound h

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
theorem continuous_mk : Continuous (mk I u) :=
  continuous_quot_mk

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
theorem surjective_mk : Function.Surjective (mk I u) :=
  Quot.mk_surjective

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
theorem isQuotientMap_mk : IsQuotientMap (mk I u) :=
  isQuotientMap_quot_mk

instance [CompactSpace S] : CompactSpace (CoincidentBranchQuotient I u) :=
  inferInstanceAs (CompactSpace (Quot _))

instance [ConnectedSpace S] : ConnectedSpace (CoincidentBranchQuotient I u) :=
  surjective_mk.connectedSpace continuous_mk

/-- **The fibres of `π` are the classes of `Γ`.** For a nonconstant `C²` pseudoholomorphic map `u`
from a compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold, two
points have the same image in `S / Γ` exactly when they are related by the closure `Γ` of the
coincident-branch relation. -/
theorem mk_eq_mk_iff [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) {z ζ : S} :
    mk I u z = mk I u ζ ↔ (z, ζ) ∈ coincidentBranchClosure I u :=
  Quot.eq.trans (equivalence_coincidentBranchClosure hu hJu hne).eqvGen_iff

/-- **Off the critical values, the fibres of `π` are the classes of the coincident-branch
relation.** For a nonconstant `C²` pseudoholomorphic map `u` from a compact connected Hausdorff
Riemann surface into a Hausdorff almost complex manifold and a point `z` outside
`B = u⁻¹(u(Crit u))`, a point `ζ` has the image of `z` in `S / Γ` exactly when the branch of `u`
at `z` factors holomorphically through the branch of `u` at `ζ`. -/
theorem mk_eq_mk_iff_of_notMem [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) {z ζ : S} (hz : z ∉ criticalValuePreimage I u) :
    mk I u z = mk I u ζ ↔ GermFactorsThrough u z u ζ :=
  (mk_eq_mk_iff hu hJu hne).trans (mem_coincidentBranchClosure_iff_of_notMem hu hJu hz)

/-! ### The induced map on the quotient -/

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
variable (I) in
/-- **The map `v : S / Γ → N` induced by `u`**, for a continuous map `u` into a Hausdorff space:
`u` takes the same value at points related by the closure `Γ` of its coincident-branch relation,
so it factors as `u = v ∘ π` (`TauCeti.CoincidentBranchQuotient.lift_comp_mk`). -/
def lift [T2Space N] (hu : Continuous u) : CoincidentBranchQuotient I u → N :=
  Quot.lift u fun _ _ h ↦ apply_eq_of_mem_coincidentBranchClosure hu h

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
@[simp]
theorem lift_mk [T2Space N] (hu : Continuous u) (z : S) : lift I hu (mk I u z) = u z :=
  (rfl)

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- **`u` factors through `S / Γ`**: `u = v ∘ π`. -/
theorem lift_comp_mk [T2Space N] (hu : Continuous u) : lift I hu ∘ mk I u = u :=
  (rfl)

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- The map `v : S / Γ → N` induced by `u` is continuous. -/
theorem continuous_lift [T2Space N] (hu : Continuous u) : Continuous (lift I hu) :=
  continuous_quot_lift _ hu

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- Points with the same image in `S / Γ` have the same image under a continuous map `u` into a
Hausdorff space. -/
theorem apply_eq_of_mk_eq [T2Space N] (hu : Continuous u) {z ζ : S}
    (h : mk I u z = mk I u ζ) : u z = u ζ :=
  congrArg (lift I hu) h

/-- **The fibres of `π` are finite**, for a nonconstant `C¹` pseudoholomorphic map from a compact
connected Riemann surface into a Hausdorff almost complex manifold: they lie in the fibres of
`u`. -/
theorem finite_preimage_mk [CompactSpace S] [PreconnectedSpace S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (q : CoincidentBranchQuotient I u) :
    (mk I u ⁻¹' {q}).Finite := by
  obtain ⟨z, rfl⟩ := surjective_mk q
  exact (finite_preimage_singleton_of_isPseudoholomorphic hu hJu hne (u z)).subset fun _ hζ ↦
    apply_eq_of_mk_eq hu.continuous hζ

/-! ### Openness and separation -/

/-- **The quotient map `π : S → S / Γ` is open.** Let `u` be a nonconstant `C²` pseudoholomorphic
map from a compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold. If
a point `a` of an open set `W` is related to `z` by the closure `Γ` of the coincident-branch
relation, then every point near `z` outside the finite set `B = u⁻¹(u(Crit u))` has a coincident
branch at a point of `W`; so the saturation of `W` is a neighbourhood of `z`. -/
theorem isOpenMap_mk [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : IsOpenMap (mk I u) := by
  intro W hW
  rw [← isQuotientMap_mk.isOpen_preimage, isOpen_iff_mem_nhds]
  rintro z ⟨a, ha, haz⟩
  -- The points near `z` other than `z` lie outside the finite set `B`.
  have hB : ((criticalValuePreimage I u) \ {z})ᶜ ∈ 𝓝 z :=
    ((finite_criticalValuePreimage (hu.of_le one_le_two) hJu hne).sdiff).isClosed.compl_mem_nhds
      fun h ↦ h.2 rfl
  filter_upwards [hB, eventually_exists_germFactorsThrough_of_mem_coincidentBranchClosure hu hJu
    hne ((mk_eq_mk_iff hu hJu hne).1 haz) (hW.mem_nhds ha)] with y hyB hy
  by_cases hyz : y = z
  · exact hyz ▸ ⟨a, ha, haz⟩
  obtain ⟨ζ, hζ, hyζ⟩ := hy fun h ↦ hyB ⟨h, hyz⟩
  exact ⟨ζ, hζ, (mk_eq_mk_of_mem_coincidentBranchClosure
    (mem_coincidentBranchClosure_of_germFactorsThrough (fun h ↦ hyB ⟨h, hyz⟩) hyζ)).symm⟩

/-- **The quotient map `π : S → S / Γ` is an open quotient map**, for a nonconstant `C²`
pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff almost
complex manifold. -/
theorem isOpenQuotientMap_mk [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : IsOpenQuotientMap (mk I u) :=
  ⟨surjective_mk, continuous_mk, isOpenMap_mk hu hJu hne⟩

/-- **The quotient `S / Γ` is Hausdorff**, for a nonconstant `C²` pseudoholomorphic map from a
compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold: the quotient
map is open and the relation `Γ` is closed. -/
theorem t2Space [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : T2Space (CoincidentBranchQuotient I u) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_mk hu hJu hne)]
  convert isClosed_coincidentBranchClosure (I := I) (u := u) using 1
  ext p
  exact mk_eq_mk_iff hu hJu hne

/-- **The quotient map `π : S → S / Γ` is closed**, for a nonconstant `C²` pseudoholomorphic map
from a compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold, being
a continuous map from a compact space to a Hausdorff space. -/
theorem isClosedMap_mk [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : IsClosedMap (mk I u) :=
  have := t2Space hu hJu hne
  continuous_mk.isClosedMap

/-! ### The covering off the critical values -/

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- **The preimage of the critical values is a union of fibres of `π`**, for a continuous map `u`
into a Hausdorff space: related points have the same image under `u`. -/
theorem preimage_image_mk_criticalValuePreimage [T2Space N] (hu : Continuous u) :
    mk I u ⁻¹' (mk I u '' criticalValuePreimage I u) = criticalValuePreimage I u := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro z ⟨b, hb, hbz⟩
  exact (mem_criticalValuePreimage_iff_of_apply_eq (apply_eq_of_mk_eq hu hbz)).1 hb

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **`π` is injective near a point off the critical values.** For a `C¹` pseudoholomorphic map
`u` into a Hausdorff almost complex manifold and a point `z ∉ u⁻¹(u(Crit u))`, the map `u` is
immersed, hence injective, near `z`, and points with the same image in `S / Γ` have the same image
under `u`. -/
theorem exists_mem_nhds_injOn_mk [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) {z : S}
    (hz : z ∉ criticalValuePreimage I u) : ∃ t ∈ 𝓝 z, InjOn (mk I u) t := by
  obtain ⟨t, ht, htinj⟩ := (hu z).exists_mem_nhds_injOn one_ne_zero
    ((hJu.isPseudoholomorphicAt z).injective_mfderiv_iff_ne_zero.2
      (mfderiv_ne_zero_of_notMem_criticalValuePreimage hz))
  exact ⟨t, ht, fun _ hy _ hy' h ↦ htinj hy hy' (apply_eq_of_mk_eq hu.continuous h)⟩

/-- **`π` is a local homeomorphism off the critical values.** For a nonconstant `C²`
pseudoholomorphic map `u` from a compact connected Hausdorff Riemann surface into a Hausdorff
almost complex manifold, the quotient map `π : S → S / Γ` restricts to a homeomorphism onto an open
set near every point outside `B = u⁻¹(u(Crit u))`: it is continuous, open, and injective near such
points. -/
theorem isLocalHomeomorphOn_mk [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : IsLocalHomeomorphOn (mk I u) (criticalValuePreimage I u)ᶜ := by
  refine (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).2 fun z hz ↦ ?_
  obtain ⟨t, ht, htinj⟩ := exists_mem_nhds_injOn_mk (hu.of_le one_le_two) hJu hz
  refine ⟨interior t, interior_mem_nhds.2 ht, .of_continuous_injective_isOpenMap
    (continuous_mk.comp continuous_subtypeVal) (fun y y' h ↦ Subtype.ext ?_)
    ((isOpenMap_mk hu hJu hne).domRestrict isOpen_interior)⟩
  exact htinj (interior_subset y.property) (interior_subset y'.property) h

/-- **`π` is a covering map off the critical values.** For a nonconstant `C²` pseudoholomorphic map
`u` from a compact connected Hausdorff Riemann surface into a Hausdorff almost complex manifold, the
quotient map `π : S → S / Γ` is a covering map over the complement of the image of the finite set
`B = u⁻¹(u(Crit u))`: it is a closed map with finite fibres, and a local homeomorphism on
`π⁻¹(π(B)ᶜ) = S \ B`. -/
theorem isCoveringMapOn_mk [CompactSpace S] [PreconnectedSpace S] [T2Space S] [T2Space N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    IsCoveringMapOn (mk I u) (mk I u '' criticalValuePreimage I u)ᶜ := by
  refine (isClosedMap_mk hu hJu hne).isCoveringMapOn_of_isLocalHomeomorphOn
    (fun q _ ↦ finite_preimage_mk (hu.of_le one_le_two) hJu hne q) ?_
  rw [preimage_compl, preimage_image_mk_criticalValuePreimage hu.continuous]
  exact isLocalHomeomorphOn_mk hu hJu hne

/-- **The degree of `π`.** For a nonconstant `C²` pseudoholomorphic map `u` from a compact connected
Hausdorff Riemann surface into a Hausdorff almost complex manifold, there is a `d ≥ 1` such that
every point of `S / Γ` outside the image of `B = u⁻¹(u(Crit u))` has exactly `d` preimages under
`π`: the number of coincident branches of `u` at a point off `B`. -/
theorem exists_pos_forall_ncard_preimage_mk_eq [CompactSpace S] [ConnectedSpace S] [T2Space S]
    [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    ∃ d : ℕ, 0 < d ∧ ∀ q ∉ mk I u '' criticalValuePreimage I u, (mk I u ⁻¹' {q}).ncard = d := by
  obtain ⟨d, hd, h⟩ := exists_pos_forall_ncard_setOf_germFactorsThrough_eq hu hJu hne
  refine ⟨d, hd, fun q hq ↦ ?_⟩
  obtain ⟨z, rfl⟩ := surjective_mk q
  have hz : z ∉ criticalValuePreimage I u := fun h ↦ hq (mem_image_of_mem _ h)
  rw [← h z hz]
  congr 1
  ext ζ
  exact eq_comm.trans (mk_eq_mk_iff_of_notMem hu hJu hne hz)

/-- **The local degree of `π` is the local multiplicity.** Let `u` be a nonconstant `C²`
pseudoholomorphic map from a compact connected Hausdorff Riemann surface into a Hausdorff almost
complex manifold. Every point `z` has a neighbourhood `V` such that for every neighbourhood
`V' ⊆ V` of `z`, every point of `S / Γ` near `π z` outside the image of `B = u⁻¹(u(Crit u))` has
exactly `e_z` preimages under `π` in `V'`, where `e_z` is the local multiplicity
`TauCeti.coincidentBranchMultiplicity` of the coincident-branch relation at `z`. -/
theorem exists_mem_nhds_forall_eventually_ncard_inter_preimage_mk_eq [CompactSpace S]
    [PreconnectedSpace S] [T2Space S] [T2Space N] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (z : S) :
    ∃ V ∈ 𝓝 z, ∀ V' ∈ 𝓝 z, V' ⊆ V → ∀ᶠ q in 𝓝 (mk I u z),
      q ∉ mk I u '' criticalValuePreimage I u →
        (V' ∩ mk I u ⁻¹' {q}).ncard = coincidentBranchMultiplicity I u z := by
  obtain ⟨V, hV, h⟩ :=
    exists_mem_nhds_forall_eventually_ncard_eq_coincidentBranchMultiplicity hu hJu hne z
  refine ⟨V, hV, fun V' hV' hV'V ↦ ?_⟩
  -- Since `π` is open, the points near `π z` are images of points near `z`.
  filter_upwards [(isOpenMap_mk hu hJu hne).image_mem_nhds (h V' hV' hV'V)]
  rintro _ ⟨w, hw, rfl⟩ hwB
  have hwB' : w ∉ criticalValuePreimage I u := fun h ↦ hwB (mem_image_of_mem _ h)
  rw [← hw hwB']
  congr 1
  ext y
  exact and_congr_right fun _ ↦ eq_comm.trans (mk_eq_mk_iff_of_notMem hu hJu hne hwB')

end CoincidentBranchQuotient

end TauCeti
