/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Node.Reduced
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Hyperplane
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback

/-!
# The coordinate critical quotient of a holomorphic node family

For the equation `xy = s(b)`, its vertical partial derivatives are `y` and `x`. This file
computes the quotient of the ambient holomorphic stalk by `(xy - s, x, y)` as the base
stalk modulo `(s)`. In particular the inverse image of this coordinate Jacobian ideal under
pullback from the base is exactly `(s)`, not its radical. Thus the calculation retains the
multiplicity of a smoothing parameter, and also applies to permanent nodes. The coordinate
critical ideal commutes with pullback by an arbitrary local holomorphic base map.

The proof uses successive restriction to the two coordinate hyperplanes, so all quotients
are of actual holomorphic germs. It does not identify algebraic Kähler differentials of
holomorphic stalks with analytic differentials, or assert coordinate independence of a
Fitting ideal. Those require a separate analytic differential comparison.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), for the local equations of nodal families.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for restriction and division of holomorphic germs.
-/

public noncomputable section

open Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (b : E)

local notation "A" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ, E) E)) b
local notation "R" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ)
    ((E × ℂ) × ℂ))) ((b, (0 : ℂ)), (0 : ℂ))

/-- Restriction of an ambient node-chart germ to `x = y = 0`. This is defined on the
ambient chart, whether or not its zero section lies on the node family. -/
def nodeBaseRestriction : R →+* A :=
  (restrictHyperplane b 0).comp (restrictHyperplane (b, (0 : ℂ)) 0)

/-- Pullback of base germs to the ambient node chart. -/
def nodeBaseExtension : A →+* R :=
  (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) Prod.fst
    contDiff_fst.contMDiff ((b, (0 : ℂ)), 0)).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst contDiff_fst.contMDiff (b, 0))

/-- Restriction to the zero section is a left inverse to pullback from the base. -/
@[simp]
theorem nodeBaseRestriction_nodeBaseExtension (s : A) :
    nodeBaseRestriction b (nodeBaseExtension b s) = s := by
  simp only [nodeBaseRestriction, nodeBaseExtension, RingHom.comp_apply]
  rw [restrictHyperplane_stalkPrecomp_fst, restrictHyperplane_stalkPrecomp_fst]

/-- Every base germ is the restriction of an ambient germ. -/
theorem nodeBaseRestriction_surjective : Function.Surjective (nodeBaseRestriction b) :=
  fun s ↦ ⟨nodeBaseExtension b s, nodeBaseRestriction_nodeBaseExtension b s⟩

/-- The first vertical coordinate of the ambient node chart, as a holomorphic germ. -/
def nodeFstCoordinate : R :=
  stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) Prod.fst contDiff_fst.contMDiff
    ((b, (0 : ℂ)), 0) (hyperplaneCoordinateGerm b 0)

/-- The second vertical coordinate of the ambient node chart, as a holomorphic germ. -/
abbrev nodeSndCoordinate : R := hyperplaneCoordinateGerm (b, (0 : ℂ)) 0

/-- The first coordinate germ is represented by the first vertical projection. -/
@[simp]
theorem toFilterGerm_nodeFstCoordinate :
    toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, (0 : ℂ)), 0)
      (𝓝 ((b, (0 : ℂ)), 0)) le_rfl (nodeFstCoordinate b) =
        (fun z : (E × ℂ) × ℂ ↦ z.1.2) := by
  simp only [nodeFstCoordinate, toFilterGerm_stalkPrecomp,
    OpenPartialHomeomorph.toFilterGerm_holomorphicLinearCoordinateGerm,
    Germ.coe_compTendsto]
  congr 1
  funext z
  simp

/-- The first coordinate restricts to zero on the zero section. -/
@[simp]
theorem nodeBaseRestriction_nodeFstCoordinate :
    nodeBaseRestriction b (nodeFstCoordinate b) = 0 := by
  simp only [nodeBaseRestriction, nodeFstCoordinate, RingHom.comp_apply]
  rw [restrictHyperplane_stalkPrecomp_fst, restrictHyperplane_hyperplaneCoordinateGerm]

/-- The second coordinate restricts to zero on the zero section. -/
@[simp]
theorem nodeBaseRestriction_nodeSndCoordinate :
    nodeBaseRestriction b (nodeSndCoordinate b) = 0 := by
  simp [nodeBaseRestriction]

/-- A germ vanishes on the zero section exactly when it belongs to `(x,y)`. -/
theorem ker_nodeBaseRestriction :
    RingHom.ker (nodeBaseRestriction b) =
      Ideal.span {nodeFstCoordinate b, nodeSndCoordinate b} := by
  let r := restrictHyperplane (b, (0 : ℂ)) 0
  have hmap : (Ideal.span {nodeFstCoordinate b}).map r =
      Ideal.span {hyperplaneCoordinateGerm b 0} := by
    simp only [r, Ideal.map_span, Set.image_singleton, nodeFstCoordinate]
    rw [restrictHyperplane_stalkPrecomp_fst]
  rw [nodeBaseRestriction, ← RingHom.comap_ker, ker_restrictHyperplane, ← hmap,
    Ideal.comap_map_of_surjective r (restrictHyperplane_surjective _ _),
    ← RingHom.ker_eq_comap_bot, ker_restrictHyperplane, Ideal.span_insert]

/-- The defining equation vanishes on the zero section precisely to the order of `s`:
its restriction is `-s`. -/
@[simp]
theorem nodeBaseRestriction_nodeEquation (s : A) :
    nodeBaseRestriction b (nodeEquation b 0 0 s) = -s := by
  obtain ⟨f, _, hf⟩ := exists_toFilterGerm_eq b s
  apply toFilterGerm_nhds_injective b
  simp only [nodeBaseRestriction, RingHom.comp_apply, toFilterGerm_restrictHyperplane]
  rw [toFilterGerm_nodeEquation b 0 0 s (hf _ le_rfl), map_neg, hf _ le_rfl,
    Germ.coe_compTendsto, Germ.coe_compTendsto, ← Germ.coe_neg]
  congr 1
  funext z
  simp

/-- The coordinate relative Jacobian ideal in the ambient holomorphic stalk:
the equation `xy-s` together with its vertical partial derivatives `x,y`. -/
def nodeCriticalIdeal (s : A) : Ideal R :=
  Ideal.span {nodeEquation b 0 0 s, nodeFstCoordinate b, nodeSndCoordinate b}

/-- The coordinate critical ideal consists of the equation and the ideal of the zero section. -/
theorem nodeCriticalIdeal_eq_span_sup_ker (s : A) :
    nodeCriticalIdeal b s = Ideal.span {nodeEquation b 0 0 s} ⊔
      RingHom.ker (nodeBaseRestriction b) := by
  rw [nodeCriticalIdeal, Ideal.span_insert, ker_nodeBaseRestriction]

/-- Restriction sends the coordinate critical ideal to the unreduced principal ideal `(s)`. -/
@[simp]
theorem map_nodeCriticalIdeal (s : A) :
    (nodeCriticalIdeal b s).map (nodeBaseRestriction b) = Ideal.span {s} := by
  simp [nodeCriticalIdeal, Ideal.map_span]

/-- The coordinate critical ideal is exactly the inverse image of `(s)` under restriction. -/
theorem nodeCriticalIdeal_eq_comap (s : A) :
    nodeCriticalIdeal b s = (Ideal.span {s}).comap (nodeBaseRestriction b) := by
  rw [← map_nodeCriticalIdeal b s,
    Ideal.comap_map_of_surjective _ (nodeBaseRestriction_surjective b),
    nodeCriticalIdeal_eq_span_sup_ker]
  simp [← RingHom.ker_eq_comap_bot]

/-- Membership in the critical ideal is detected by divisibility of the zero-section
restriction by the smoothing parameter. -/
@[simp]
theorem mem_nodeCriticalIdeal_iff (s : A) (f : R) :
    f ∈ nodeCriticalIdeal b s ↔ s ∣ nodeBaseRestriction b f := by
  rw [nodeCriticalIdeal_eq_comap, Ideal.mem_comap, Ideal.mem_span_singleton]

/-- The ideal on the base cut out by the coordinate critical quotient is exactly `(s)`.
No reduction or nonvanishing assumption on the smoothing germ is needed. -/
@[simp]
theorem comap_nodeCriticalIdeal (s : A) :
    (nodeCriticalIdeal b s).comap (nodeBaseExtension b) = Ideal.span {s} := by
  ext f
  simp [Ideal.mem_comap, mem_nodeCriticalIdeal_iff, Ideal.mem_span_singleton]

/-- Restriction identifies the coordinate critical quotient with the base modulo `(s)`. -/
def nodeCriticalQuotientEquiv (s : A) : (R ⧸ nodeCriticalIdeal b s) ≃+* (A ⧸ Ideal.span {s}) :=
  (Ideal.quotEquivOfEq (by
    rw [← RingHom.comap_ker, Ideal.mk_ker, ← nodeCriticalIdeal_eq_comap])).trans
      (((Ideal.Quotient.mk (Ideal.span {s})).comp
        (nodeBaseRestriction b)).quotientKerEquivOfSurjective
          (Ideal.Quotient.mk_surjective.comp (nodeBaseRestriction_surjective b)))

/-- The critical-quotient comparison is restriction to the zero section on representatives. -/
@[simp]
theorem nodeCriticalQuotientEquiv_mk (s : A) (f : R) :
    nodeCriticalQuotientEquiv b s (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (nodeBaseRestriction b f) := by
  simp [nodeCriticalQuotientEquiv]

/-- The inverse critical-quotient comparison is induced by pullback of base germs. -/
@[simp]
theorem nodeCriticalQuotientEquiv_symm_mk (s f : A) :
    (nodeCriticalQuotientEquiv b s).symm (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (nodeBaseExtension b f) := by
  apply (nodeCriticalQuotientEquiv b s).injective
  simp

/-- For a permanent node the critical ideal is just `(x,y)`, leaving the entire base. -/
@[simp]
theorem nodeCriticalIdeal_zero :
    nodeCriticalIdeal b 0 = Ideal.span {nodeFstCoordinate b, nodeSndCoordinate b} := by
  rw [nodeCriticalIdeal_eq_comap, Ideal.span_singleton_zero, ← RingHom.ker_eq_comap_bot,
    ker_nodeBaseRestriction]

/-! ## Local analytic base change -/

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {φ : F → E} {a : F}
  (hφ : ∀ᶠ z in 𝓝 a, ContMDiffAt 𝓘(ℂ, F) 𝓘(ℂ, E) ω φ z)

include hφ in
private theorem eventually_contMDiffAt_nodeBaseChange :
    ∀ᶠ z in 𝓝 ((a, (0 : ℂ)), (0 : ℂ)),
      ContMDiffAt 𝓘(ℂ, (F × ℂ) × ℂ) 𝓘(ℂ, (E × ℂ) × ℂ) ω
        (fun z ↦ ((φ z.1.1, z.1.2), z.2)) z := by
  have ht : Tendsto (fun z : (F × ℂ) × ℂ ↦ z.1.1)
      (𝓝 ((a, (0 : ℂ)), 0)) (𝓝 a) := continuous_fst.fst.continuousAt.tendsto
  filter_upwards [ht.eventually hφ] with z hz
  apply contMDiffAt_iff_contDiffAt.mpr
  exact (((contMDiffAt_iff_contDiffAt.mp hz).comp z
    (contDiffAt_fst.comp z contDiffAt_fst)).prodMk
      (contDiffAt_snd.comp z contDiffAt_fst)).prodMk contDiffAt_snd

/-- Pullback of ambient node-chart germs by a local analytic base map, leaving the two
vertical coordinates unchanged. No global extension of the base map is required. -/
def nodeAmbientPullback :
    (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk
        ((φ a, (0 : ℂ)), 0) →+*
      (holomorphicStructureSheaf 𝓘(ℂ, (F × ℂ) × ℂ) ((F × ℂ) × ℂ)).presheaf.stalk
        ((a, (0 : ℂ)), 0) :=
  stalkPullback (eventually_contMDiffAt_nodeBaseChange hφ)

/-- On function representatives the ambient pullback composes only the base coordinate. -/
theorem toFilterGerm_nodeAmbientPullback
    {s : (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk
      ((φ a, (0 : ℂ)), 0)} {f : (E × ℂ) × ℂ → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((φ a, (0 : ℂ)), 0)
      (𝓝 ((φ a, (0 : ℂ)), 0)) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, (F × ℂ) × ℂ) ((F × ℂ) × ℂ) ((a, (0 : ℂ)), 0)
      (𝓝 ((a, (0 : ℂ)), 0)) le_rfl (nodeAmbientPullback hφ s) =
        (fun z : (F × ℂ) × ℂ ↦ f ((φ z.1.1, z.1.2), z.2)) := by
  rw [nodeAmbientPullback, toFilterGerm_stalkPullback, hs, Germ.coe_compTendsto]
  simp only [Function.comp_def]

/-- Local analytic base change fixes the first vertical coordinate. -/
@[simp]
theorem nodeAmbientPullback_nodeFstCoordinate :
    nodeAmbientPullback hφ (nodeFstCoordinate (φ a)) = nodeFstCoordinate a := by
  apply toFilterGerm_nhds_injective ((a, (0 : ℂ)), 0)
  rw [toFilterGerm_nodeAmbientPullback hφ (toFilterGerm_nodeFstCoordinate (φ a)),
    toFilterGerm_nodeFstCoordinate]

/-- Local analytic base change fixes the second vertical coordinate. -/
@[simp]
theorem nodeAmbientPullback_nodeSndCoordinate :
    nodeAmbientPullback hφ (nodeSndCoordinate (φ a)) = nodeSndCoordinate a := by
  apply toFilterGerm_nhds_injective ((a, (0 : ℂ)), 0)
  rw [toFilterGerm_nodeAmbientPullback hφ (f := Prod.snd) (by simp)]
  simp

/-- The pulled-back node equation has the pulled-back smoothing germ. -/
@[simp]
theorem nodeAmbientPullback_nodeEquation
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk (φ a)) :
    nodeAmbientPullback hφ (nodeEquation (φ a) 0 0 s) =
      nodeEquation a 0 0 (stalkPullback hφ s) := by
  obtain ⟨f, _, hf⟩ := exists_toFilterGerm_eq (φ a) s
  have hfs := hf (𝓝 (φ a)) le_rfl
  apply toFilterGerm_nhds_injective ((a, (0 : ℂ)), 0)
  rw [toFilterGerm_nodeAmbientPullback hφ (toFilterGerm_nodeEquation (φ a) 0 0 s hfs),
    toFilterGerm_nodeEquation a 0 0 _ (by
      rw [toFilterGerm_stalkPullback, hfs, Germ.coe_compTendsto])]
  simp only [Function.comp_def]

/-- The coordinate relative Jacobian ideal commutes with every local analytic base change,
including non-submersive base maps and identically vanishing smoothing parameters. -/
theorem map_nodeCriticalIdeal_nodeAmbientPullback
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk (φ a)) :
    (nodeCriticalIdeal (φ a) s).map (nodeAmbientPullback hφ) =
      nodeCriticalIdeal a (stalkPullback hφ s) := by
  simp [nodeCriticalIdeal, Ideal.map_span]

end TauCeti.holomorphicStructureSheaf
