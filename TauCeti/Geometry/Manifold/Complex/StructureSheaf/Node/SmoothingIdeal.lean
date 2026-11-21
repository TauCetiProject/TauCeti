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
are of actual holomorphic germs. The restrictions of the node coordinates and of base germs to
the plane `x = 0` (`TauCeti.holomorphicStructureSheaf.nodeFstZeroRestriction`) and to the plane
`y = 0` are computed explicitly. It does not identify algebraic Kähler differentials of
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
local notation "B" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ))) (b, (0 : ℂ))

/-- Restriction of an ambient node-chart germ to `x = y = 0`. This is defined on the
ambient chart, whether or not its zero section lies on the node family. -/
def nodeBaseRestriction : R →+* A :=
  (restrictHyperplane b 0).comp (restrictHyperplane (b, (0 : ℂ)) 0)

/-- Pullback of base germs to the ambient node chart. -/
def nodeBaseExtension : A →+* R :=
  (stalkPrecomp 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) Prod.fst
    contDiff_fst.contMDiff ((b, (0 : ℂ)), 0)).comp
      (stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst contDiff_fst.contMDiff (b, 0))

/-- The local ring `𝒪 ⧸ (xy - s(b))` of the node is an algebra over the base germs at `b`, by
pullback of base germs to the node chart. -/
instance nodeLocalAlgebra (s : A) : Algebra A (R ⧸ Ideal.span {nodeEquation b 0 0 s}) :=
  ((Ideal.Quotient.mk _).comp (nodeBaseExtension b)).toAlgebra

@[simp]
theorem algebraMap_nodeLocalAlgebra (s a : A) :
    algebraMap A (R ⧸ Ideal.span {nodeEquation b 0 0 s}) a =
      Ideal.Quotient.mk _ (nodeBaseExtension b a) :=
  rfl

/-- Restriction of a function representative evaluates both vertical coordinates at zero. -/
theorem toFilterGerm_nodeBaseRestriction {s : R} {f : (E × ℂ) × ℂ → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, (0 : ℂ)), 0)
      (𝓝 ((b, (0 : ℂ)), 0)) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl (nodeBaseRestriction b s) =
      (fun e ↦ f ((e, 0), 0)) := by
  rw [nodeBaseRestriction, RingHom.comp_apply, toFilterGerm_restrictHyperplane,
    toFilterGerm_restrictHyperplane, hs, Germ.coe_compTendsto, Germ.coe_compTendsto]
  rfl

/-- Extension of a function representative forgets both vertical coordinates. -/
theorem toFilterGerm_nodeBaseExtension {s : A} {f : E → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, E) E b (𝓝 b) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, (0 : ℂ)), 0)
      (𝓝 ((b, (0 : ℂ)), 0)) le_rfl (nodeBaseExtension b s) =
        (fun z : (E × ℂ) × ℂ ↦ f z.1.1) := by
  rw [nodeBaseExtension, RingHom.comp_apply, toFilterGerm_stalkPrecomp,
    toFilterGerm_stalkPrecomp, hs, Germ.coe_compTendsto, Germ.coe_compTendsto]
  rfl

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
def nodeSndCoordinate : R := hyperplaneCoordinateGerm (b, (0 : ℂ)) 0

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

/-- The second coordinate germ is represented by the second vertical projection. -/
@[simp]
theorem toFilterGerm_nodeSndCoordinate :
    toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, (0 : ℂ)), 0)
      (𝓝 ((b, (0 : ℂ)), 0)) le_rfl (nodeSndCoordinate b) =
        (fun z : (E × ℂ) × ℂ ↦ z.2) := by
  simp [nodeSndCoordinate,
    OpenPartialHomeomorph.toFilterGerm_holomorphicLinearCoordinateGerm]

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
  simp only [nodeBaseRestriction, nodeSndCoordinate, RingHom.comp_apply]
  rw [restrictHyperplane_hyperplaneCoordinateGerm, map_zero]

/-- Restriction of an ambient node-chart germ to the plane `x = 0`, with coordinates `(b, y)`. -/
def nodeFstZeroRestriction : R →+* B :=
  stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) (fun w ↦ ((w.1, (0 : ℂ)), w.2))
    (contMDiff_iff_contDiff.mpr (by fun_prop)) (b, 0)

/-- Restriction of a function representative to `x = 0` sets the first vertical coordinate to
zero. -/
theorem toFilterGerm_nodeFstZeroRestriction {s : R} {f : (E × ℂ) × ℂ → ℂ}
    (hs : toFilterGerm 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ) ((b, (0 : ℂ)), 0)
      (𝓝 ((b, (0 : ℂ)), 0)) le_rfl s = f) :
    toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (b, 0) (𝓝 (b, 0)) le_rfl (nodeFstZeroRestriction b s) =
      (fun w : E × ℂ ↦ f ((w.1, 0), w.2)) := by
  rw [nodeFstZeroRestriction, toFilterGerm_stalkPrecomp, hs, Germ.coe_compTendsto]
  -- `f ∘ (fun w ↦ ((w.1, 0), w.2))` is the displayed function by definition of composition.
  rfl

@[simp]
theorem nodeFstZeroRestriction_nodeFstCoordinate :
    nodeFstZeroRestriction b (nodeFstCoordinate b) = 0 := by
  apply toFilterGerm_nhds_injective (b, (0 : ℂ))
  rw [toFilterGerm_nodeFstZeroRestriction b (toFilterGerm_nodeFstCoordinate b), map_zero]
  simp [← Germ.coe_zero, Pi.zero_def]

@[simp]
theorem nodeFstZeroRestriction_nodeSndCoordinate :
    nodeFstZeroRestriction b (nodeSndCoordinate b) = hyperplaneCoordinateGerm b 0 := by
  apply toFilterGerm_nhds_injective (b, (0 : ℂ))
  rw [toFilterGerm_nodeFstZeroRestriction b (toFilterGerm_nodeSndCoordinate b),
    OpenPartialHomeomorph.toFilterGerm_holomorphicLinearCoordinateGerm]
  congr 1
  funext w
  simp

/-- Restricting a base germ pulled back to the node chart to the plane `x = 0` gives the same
base germ pulled back to `(b, y)`. -/
@[simp]
theorem nodeFstZeroRestriction_nodeBaseExtension (a : A) :
    nodeFstZeroRestriction b (nodeBaseExtension b a) =
      stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst contDiff_fst.contMDiff (b, 0) a := by
  obtain ⟨f, _, hf⟩ := exists_toFilterGerm_eq b a
  apply toFilterGerm_nhds_injective (b, (0 : ℂ))
  rw [toFilterGerm_nodeFstZeroRestriction b (toFilterGerm_nodeBaseExtension b (hf _ le_rfl)),
    toFilterGerm_stalkPrecomp, hf _ le_rfl, Germ.coe_compTendsto]
  -- Both sides are `f` composed with the projection `(b, w) ↦ b`.
  congr 1

@[simp]
theorem restrictHyperplane_nodeFstCoordinate :
    restrictHyperplane (b, (0 : ℂ)) 0 (nodeFstCoordinate b) = hyperplaneCoordinateGerm b 0 :=
  restrictHyperplane_stalkPrecomp_fst (b, (0 : ℂ)) 0 (hyperplaneCoordinateGerm b 0)

@[simp]
theorem restrictHyperplane_nodeSndCoordinate :
    restrictHyperplane (b, (0 : ℂ)) 0 (nodeSndCoordinate b) = 0 :=
  restrictHyperplane_hyperplaneCoordinateGerm (b, (0 : ℂ)) 0

/-- Restricting a base germ pulled back to the node chart to the plane `y = 0` gives the same
base germ pulled back to `(b, x)`. -/
@[simp]
theorem restrictHyperplane_nodeBaseExtension (a : A) :
    restrictHyperplane (b, (0 : ℂ)) 0 (nodeBaseExtension b a) =
      stalkPrecomp 𝓘(ℂ, E × ℂ) (E × ℂ) Prod.fst contDiff_fst.contMDiff (b, 0) a := by
  simp only [nodeBaseExtension, RingHom.comp_apply]
  exact restrictHyperplane_stalkPrecomp_fst (b, 0) 0 _

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
    ← RingHom.ker_eq_comap_bot, ker_restrictHyperplane, Ideal.span_insert, nodeSndCoordinate]

/-- Every germ is its value on the zero section, pulled back from the base, plus an element of
`(x,y)`. -/
theorem exists_eq_nodeBaseExtension_add (f : R) :
    ∃ g g' : R, f = nodeBaseExtension b (nodeBaseRestriction b f) +
      (g * nodeFstCoordinate b + g' * nodeSndCoordinate b) := by
  have hker : f - nodeBaseExtension b (nodeBaseRestriction b f) ∈
      Ideal.span {nodeFstCoordinate b, nodeSndCoordinate b} := by
    rw [← ker_nodeBaseRestriction, RingHom.mem_ker, map_sub,
      nodeBaseRestriction_nodeBaseExtension, sub_self]
  obtain ⟨g, g', hg⟩ := Ideal.mem_span_pair.1 hker
  exact ⟨g, g', by rw [hg]; ring⟩

/-- In the ambient coordinates the node equation is `xy - s(b)`, with `s` pulled back from
the base. -/
theorem nodeEquation_eq_mul_sub (s : A) :
    nodeEquation b 0 0 s = nodeFstCoordinate b * nodeSndCoordinate b - nodeBaseExtension b s := by
  obtain ⟨f, _, hf⟩ := exists_toFilterGerm_eq b s
  apply toFilterGerm_nhds_injective ((b, (0 : ℂ)), (0 : ℂ))
  rw [toFilterGerm_nodeEquation b 0 0 s (hf _ le_rfl), map_sub, map_mul,
    toFilterGerm_nodeFstCoordinate, toFilterGerm_nodeSndCoordinate,
    toFilterGerm_nodeBaseExtension b (hf _ le_rfl), ← Germ.coe_mul, ← Germ.coe_sub]
  simp [Pi.mul_def, Pi.sub_def]

/-- The defining equation vanishes on the zero section precisely to the order of `s`:
its restriction is `-s`. -/
@[simp]
theorem nodeBaseRestriction_nodeEquation (s : A) :
    nodeBaseRestriction b (nodeEquation b 0 0 s) = -s := by
  obtain ⟨f, _, hf⟩ := exists_toFilterGerm_eq b s
  apply toFilterGerm_nhds_injective b
  rw [toFilterGerm_nodeBaseRestriction b (toFilterGerm_nodeEquation b 0 0 s (hf _ le_rfl)),
    map_neg, hf _ le_rfl, ← Germ.coe_neg]
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
theorem map_nodeBaseRestriction_nodeCriticalIdeal (s : A) :
    (nodeCriticalIdeal b s).map (nodeBaseRestriction b) = Ideal.span {s} := by
  simp [nodeCriticalIdeal, Ideal.map_span]

/-- The coordinate critical ideal is exactly the inverse image of `(s)` under restriction. -/
theorem nodeCriticalIdeal_eq_comap (s : A) :
    nodeCriticalIdeal b s = (Ideal.span {s}).comap (nodeBaseRestriction b) := by
  rw [← map_nodeBaseRestriction_nodeCriticalIdeal b s,
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
theorem comap_nodeBaseExtension_nodeCriticalIdeal (s : A) :
    (nodeCriticalIdeal b s).comap (nodeBaseExtension b) = Ideal.span {s} := by
  ext f
  simp [Ideal.mem_comap, mem_nodeCriticalIdeal_iff, Ideal.mem_span_singleton]

/-- The image of the coordinate critical ideal in the local ring `𝒪 ⧸ (xy - s)` of the node
is `(x, y)`. -/
theorem map_mk_nodeCriticalIdeal (s : A) :
    (nodeCriticalIdeal b s).map (Ideal.Quotient.mk (Ideal.span {nodeEquation b 0 0 s})) =
      Ideal.span {Ideal.Quotient.mk _ (nodeFstCoordinate b),
        Ideal.Quotient.mk _ (nodeSndCoordinate b)} := by
  rw [nodeCriticalIdeal_eq_span_sup_ker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
    ker_nodeBaseRestriction, Ideal.map_span, Set.image_pair]

/-- The image of the coordinate critical ideal in the local ring `𝒪 ⧸ (xy - s)` of the node
pulls back to the ideal `(s)` of the base. -/
theorem comap_map_mk_nodeCriticalIdeal (s : A) :
    ((nodeCriticalIdeal b s).map (Ideal.Quotient.mk (Ideal.span {nodeEquation b 0 0 s}))).comap
      (algebraMap A (R ⧸ Ideal.span {nodeEquation b 0 0 s})) = Ideal.span {s} := by
  have hle : Ideal.span {nodeEquation b 0 0 s} ≤ nodeCriticalIdeal b s :=
    nodeCriticalIdeal_eq_span_sup_ker b s ▸ le_sup_left
  have halg : algebraMap A (R ⧸ Ideal.span {nodeEquation b 0 0 s}) =
      (Ideal.Quotient.mk _).comp (nodeBaseExtension b) :=
    RingHom.ext (algebraMap_nodeLocalAlgebra b s)
  rw [halg, ← Ideal.comap_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hle,
    comap_nodeBaseExtension_nodeCriticalIdeal]

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

/-- Restriction to the zero section commutes with local analytic base change. -/
@[simp]
theorem nodeBaseRestriction_nodeAmbientPullback
    (s : (holomorphicStructureSheaf 𝓘(ℂ, (E × ℂ) × ℂ) ((E × ℂ) × ℂ)).presheaf.stalk
      ((φ a, (0 : ℂ)), 0)) :
    nodeBaseRestriction a (nodeAmbientPullback hφ s) =
      stalkPullback hφ (nodeBaseRestriction (φ a) s) := by
  obtain ⟨f, _, hf⟩ := exists_toFilterGerm_eq ((φ a, (0 : ℂ)), 0) s
  apply toFilterGerm_nhds_injective a
  rw [toFilterGerm_nodeBaseRestriction a
      (toFilterGerm_nodeAmbientPullback hφ (hf _ le_rfl)),
    toFilterGerm_stalkPullback, toFilterGerm_nodeBaseRestriction (φ a) (hf _ le_rfl),
    Germ.coe_compTendsto]
  rfl

/-- Extension from the base commutes with local analytic base change. -/
@[simp]
theorem nodeAmbientPullback_nodeBaseExtension
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk (φ a)) :
    nodeAmbientPullback hφ (nodeBaseExtension (φ a) s) =
      nodeBaseExtension a (stalkPullback hφ s) := by
  obtain ⟨f, _, hf⟩ := exists_toFilterGerm_eq (φ a) s
  apply toFilterGerm_nhds_injective ((a, (0 : ℂ)), 0)
  rw [toFilterGerm_nodeAmbientPullback hφ (toFilterGerm_nodeBaseExtension (φ a) (hf _ le_rfl)),
    toFilterGerm_nodeBaseExtension a (by
      rw [toFilterGerm_stalkPullback, hf _ le_rfl, Germ.coe_compTendsto])]
  rfl

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
  rw [toFilterGerm_nodeAmbientPullback hφ (toFilterGerm_nodeSndCoordinate (φ a)),
    toFilterGerm_nodeSndCoordinate]

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

/-- The critical-quotient comparison commutes with the quotient maps induced by base change. -/
theorem nodeCriticalQuotientEquiv_nodeAmbientPullback
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk (φ a))
    (q : _ ⧸ nodeCriticalIdeal (φ a) s) :
    nodeCriticalQuotientEquiv a (stalkPullback hφ s)
        (Ideal.quotientMap _ (nodeAmbientPullback hφ)
          (Ideal.map_le_iff_le_comap.mp
            (map_nodeCriticalIdeal_nodeAmbientPullback hφ s).le) q) =
      Ideal.quotientMap _ (stalkPullback hφ)
        (Ideal.map_le_iff_le_comap.mp (by simp [Ideal.map_span]))
        (nodeCriticalQuotientEquiv (φ a) s q) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

end TauCeti.holomorphicStructureSheaf
