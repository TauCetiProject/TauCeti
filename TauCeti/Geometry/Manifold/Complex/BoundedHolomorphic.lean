/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Analysis.Complex.HolomorphicFunctions.Bounded
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Bounded holomorphic maps on an open subset of a complex manifold

For an open subset `W` of a complex manifold `X` modelled by `I`, and a complex normed space
`F`, `TauCeti.boundedHolomorphicSections I F W` is the space `H^∞(W, F)` of bounded holomorphic
maps `W → F`, as a complex subspace of the bounded continuous maps `W →ᵇ F` with the supremum
norm. For `F = ℂ` these are the bounded sections of the holomorphic structure sheaf over `W`.
Holomorphy can be checked on any ambient representative `X → F`, and every element has its zero
extension `TauCeti.BoundedHolomorphicSections.extend` as a canonical ambient representative.
Restriction to a smaller open set is a continuous linear map of norm at most one
(`TauCeti.BoundedHolomorphicSections.restrict`), and these maps are functorial.

This is the manifold counterpart of `TauCeti.boundedHolomorphicFunctions`, which treats open
subsets of a complex normed space; on the model space itself the two subspaces coincide
(`TauCeti.boundedHolomorphicSections_modelWithCornersSelf`). For `X` without boundary, the two
analytic properties below are proved by reading maps in the extended charts of `X`:

* **Completeness.** For complete `F`, `H^∞(W, F)` is closed in `W →ᵇ F` (a uniform limit of
  holomorphic maps is holomorphic), hence a Banach space
  (`TauCeti.isClosed_boundedHolomorphicSections`).
* **Compactness (Montel).** If `W'` lies in a compact subset of `W` and `F` is proper,
  restriction `H^∞(W, F) → H^∞(W', F)` is a compact operator
  (`TauCeti.BoundedHolomorphicSections.isCompactOperator_restrict`): the Cauchy estimate in a
  chart (`TauCeti.BoundedHolomorphicSections.dist_apply_le_of_ball_subset`) makes the unit ball
  of `H^∞(W, F)` equicontinuous, and the Arzelà–Ascoli theorem applies.

For `F = ℂ` and a finite cover of a compact Riemann surface, products of these Banach spaces over
the members of the cover and their intersections are the spaces of Čech cochains in the
finiteness proof for the first cohomology of the structure sheaf.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer,
  1981, §14 (Montel's theorem 14.2 and the Banach spaces of cochains 14.3–14.6, there with `L²`
  rather than supremum norms).
-/

public section

open Filter Metric Set Topology TopologicalSpace BoundedContinuousFunction
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The space `H^∞(W, F)` of bounded holomorphic maps on an open set `W` of a complex manifold,
as a subspace of the bounded continuous maps `W →ᵇ F` with the supremum norm. A bounded
continuous map belongs to it when some ambient map `X → F` agreeing with it on `W` is holomorphic
on `W`. -/
def boundedHolomorphicSections (W : Opens X) : Submodule ℂ (W →ᵇ F) where
  carrier := {f | ∃ g : X → F, MDifferentiableOn I 𝓘(ℂ, F) g W ∧ ∀ z : W, g z = f z}
  zero_mem' := ⟨0, mdifferentiableOn_const, fun _ => rfl⟩
  add_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g + k, hg.add hk, fun z => by simp [hgf, hkh]⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hgf⟩
    exact ⟨c • g, hg.const_smul c, fun z => by simp [hgf]⟩

variable {I F}

/-- Membership means having an ambient holomorphic representative. -/
theorem mem_boundedHolomorphicSections_iff {W : Opens X} {f : W →ᵇ F} :
    f ∈ boundedHolomorphicSections I F W ↔
      ∃ g : X → F, MDifferentiableOn I 𝓘(ℂ, F) g W ∧ ∀ z : W, g z = f z := Iff.rfl

/-- Holomorphy can be tested on any ambient map agreeing with `f` on `W`. -/
theorem mem_boundedHolomorphicSections_iff_of_eqOn {W : Opens X} {f : W →ᵇ F} {g : X → F}
    (hgf : ∀ z : W, g z = f z) :
    f ∈ boundedHolomorphicSections I F W ↔ MDifferentiableOn I 𝓘(ℂ, F) g W := by
  constructor
  · rintro ⟨k, hk, hkf⟩
    exact hk.congr fun z hz => (hgf ⟨z, hz⟩).trans (hkf ⟨z, hz⟩).symm
  · exact fun hg => ⟨g, hg, hgf⟩

/-- Equivalently, the extension by zero is holomorphic on `W`. -/
theorem mem_boundedHolomorphicSections_iff_extend {W : Opens X} {f : W →ᵇ F} :
    f ∈ boundedHolomorphicSections I F W ↔
      MDifferentiableOn I 𝓘(ℂ, F) (Function.extend Subtype.val f (fun _ => 0)) W :=
  mem_boundedHolomorphicSections_iff_of_eqOn fun z =>
    Subtype.val_injective.extend_apply f (fun _ => 0) z

/-- Membership is equivalent to holomorphy on the open submanifold itself. -/
theorem mem_boundedHolomorphicSections_iff_mdifferentiable {W : Opens X} {f : W →ᵇ F} :
    f ∈ boundedHolomorphicSections I F W ↔ MDifferentiable I 𝓘(ℂ, F) f := by
  rw [mem_boundedHolomorphicSections_iff_extend]
  have hext : (Function.extend Subtype.val f (fun _ => 0)) ∘ (Subtype.val : W → X) = f :=
    funext (Subtype.val_injective.extend_apply f (fun _ => 0))
  constructor
  · intro hf
    have h : MDifferentiable I 𝓘(ℂ, F)
        ((Function.extend Subtype.val f (fun _ => 0)) ∘ (Subtype.val : W → X)) := fun z =>
      (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val _ z).mp
        (hf.mdifferentiableAt (W.isOpen.mem_nhds z.2))
    rwa [hext] at h
  · intro hf z hz
    rw [← hext] at hf
    have h : MDifferentiableAt I 𝓘(ℂ, F) (Function.extend Subtype.val f (fun _ => 0)) z :=
      (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val _
        (⟨z, hz⟩ : W)).mpr (hf ⟨z, hz⟩)
    exact h.mdifferentiableWithinAt

/-- On an open subset of a complex normed space, viewed as a manifold over itself, the bounded
holomorphic maps are those of `TauCeti.boundedHolomorphicFunctions`. -/
theorem boundedHolomorphicSections_modelWithCornersSelf (U : Opens E) :
    boundedHolomorphicSections 𝓘(ℂ, E) F U = boundedHolomorphicFunctions F U :=
  Submodule.ext fun _ => by
    rw [mem_boundedHolomorphicSections_iff, mem_boundedHolomorphicFunctions_iff]
    exact exists_congr fun _ => and_congr_left' mdifferentiableOn_iff_differentiableOn

section Complete

variable [IsManifold I 1 X] [I.Boundaryless] [CompleteSpace F]

/-- For complete `F`, the bounded holomorphic maps form a closed subspace of the bounded
continuous maps: a uniform limit of holomorphic maps is holomorphic. -/
theorem isClosed_boundedHolomorphicSections (W : Opens X) :
    IsClosed (boundedHolomorphicSections I F W : Set (W →ᵇ F)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨S, hS, hSf⟩ := mem_closure_iff_seq_limit.mp hf
  choose G hG hGF using hS
  have hext : ∀ z : W, Function.extend Subtype.val f (fun _ => 0) z = f z :=
    Subtype.val_injective.extend_apply f (fun _ => 0)
  refine mem_boundedHolomorphicSections_iff_extend.mpr fun x hx =>
    (mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.mpr ?_).mdifferentiableWithinAt
  -- Read the sequence in the chart at `x`: there it converges uniformly on an open set of the
  -- model space, so the limit is holomorphic there.
  set φ := extChartAt I x
  have hO : IsOpen (φ.target ∩ φ.symm ⁻¹' W) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) W.isOpen
  have hxO : φ x ∈ φ.target ∩ φ.symm ⁻¹' W :=
    ⟨mem_extChartAt_target x, by simpa [φ, extChartAt_to_inv] using hx⟩
  refine (TendstoUniformlyOn.differentiableOn (l := atTop) ?_
    (Eventually.of_forall fun n => (hG n).differentiableOn_comp_extChartAt_symm x) hO
    |>.differentiableAt (hO.mem_nhds hxO))
  have hT := Metric.tendstoUniformly_iff.mp (tendsto_iff_tendstoUniformly.mp hSf)
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => (hT ε hε).mono fun n hn y hy => ?_
  simp only [Function.comp_apply]
  rw [hext ⟨_, hy.2⟩, hGF n ⟨_, hy.2⟩]
  exact hn _

/-- For complete `F`, the bounded holomorphic maps form a Banach space. -/
instance (W : Opens X) : CompleteSpace (boundedHolomorphicSections I F W) :=
  (isClosed_boundedHolomorphicSections W).completeSpace_coe

end Complete

namespace BoundedHolomorphicSections

variable {W W' W'' : Opens X}

/-- Bounded holomorphic maps are determined by their values. -/
@[ext]
theorem ext {f g : boundedHolomorphicSections I F W} (h : ∀ z, (f : W →ᵇ F) z = (g : W →ᵇ F) z) :
    f = g :=
  Subtype.ext (BoundedContinuousFunction.ext h)

/-- A bounded holomorphic map is holomorphic on its open submanifold. -/
theorem mdifferentiable (f : boundedHolomorphicSections I F W) :
    MDifferentiable I 𝓘(ℂ, F) (f : W →ᵇ F) :=
  mem_boundedHolomorphicSections_iff_mdifferentiable.mp f.property

/-- Bundle a bounded holomorphic map defined on the open submanifold itself. -/
noncomputable def ofMDifferentiable (g : W → F) (hg : MDifferentiable I 𝓘(ℂ, F) g) (C : ℝ)
    (hC : ∀ z, ‖g z‖ ≤ C) : boundedHolomorphicSections I F W :=
  ⟨.ofNormedAddCommGroup g hg.continuous C hC,
    mem_boundedHolomorphicSections_iff_mdifferentiable.mpr hg⟩

@[simp]
theorem ofMDifferentiable_apply (g : W → F) (hg : MDifferentiable I 𝓘(ℂ, F) g) (C : ℝ)
    (hC : ∀ z, ‖g z‖ ≤ C) (z : W) :
    (ofMDifferentiable g hg C hC : W →ᵇ F) z = g z := (rfl)

/-- Restrict an ambient map, holomorphic on `W` and bounded there by `C`, to an element of
`H^∞(W, F)`. -/
noncomputable def of (W : Opens X) (g : X → F) (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (C : ℝ)
    (hC : ∀ z ∈ W, ‖g z‖ ≤ C) : boundedHolomorphicSections I F W :=
  ⟨.ofNormedAddCommGroup (fun z : W => g z) hg.continuousOn.domRestrict C fun z => hC z z.2,
    g, hg, fun _ => rfl⟩

@[simp]
theorem of_apply (g : X → F) (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (C : ℝ)
    (hC : ∀ z ∈ W, ‖g z‖ ≤ C) (z : W) : (of W g hg C hC : W →ᵇ F) z = g z := (rfl)

/-- An ambient bound is also a bound for the supremum norm. -/
theorem norm_of_le (g : X → F) (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) {C : ℝ}
    (hC : ∀ z ∈ W, ‖g z‖ ≤ C) (hC₀ : 0 ≤ C) : ‖of W g hg C hC‖ ≤ C :=
  (BoundedContinuousFunction.norm_le hC₀).mpr fun z => hC z z.2

/-- The ambient representative obtained by extending by zero. -/
noncomputable def extend (f : boundedHolomorphicSections I F W) : X → F :=
  Function.extend Subtype.val (f : W →ᵇ F) (fun _ => 0)

@[simp]
theorem extend_apply (f : boundedHolomorphicSections I F W) (z : W) :
    extend f z = (f : W →ᵇ F) z :=
  Subtype.val_injective.extend_apply _ _ _

/-- The zero extension agrees with the map at every ambient point in `W`. -/
theorem extend_apply_of_mem (f : boundedHolomorphicSections I F W) {z : X} (hz : z ∈ W) :
    extend f z = (f : W →ᵇ F) ⟨z, hz⟩ :=
  extend_apply f ⟨z, hz⟩

/-- The zero extension vanishes off `W`. -/
@[simp]
theorem extend_apply_of_notMem (f : boundedHolomorphicSections I F W) {z : X} (hz : z ∉ W) :
    extend f z = 0 :=
  Function.extend_apply' _ _ _ fun ⟨w, hw⟩ => hz (hw ▸ w.property)

/-- Zero extension preserves zero. -/
@[simp]
theorem extend_zero : extend (0 : boundedHolomorphicSections I F W) = 0 := by
  funext z
  by_cases hz : z ∈ W
  · simp [extend_apply_of_mem, hz]
  · simp [extend_apply_of_notMem, hz]

/-- Zero extension preserves addition. -/
@[simp]
theorem extend_add (f g : boundedHolomorphicSections I F W) :
    extend (f + g) = extend f + extend g := by
  funext z
  by_cases hz : z ∈ W
  · simp [extend_apply_of_mem, hz]
  · simp [extend_apply_of_notMem, hz]

/-- Zero extension preserves negation. -/
@[simp]
theorem extend_neg (f : boundedHolomorphicSections I F W) : extend (-f) = -extend f := by
  funext z
  by_cases hz : z ∈ W
  · simp [extend_apply_of_mem, hz]
  · simp [extend_apply_of_notMem, hz]

/-- Zero extension preserves subtraction. -/
@[simp]
theorem extend_sub (f g : boundedHolomorphicSections I F W) :
    extend (f - g) = extend f - extend g := by
  funext z
  by_cases hz : z ∈ W
  · simp [extend_apply_of_mem, hz]
  · simp [extend_apply_of_notMem, hz]

/-- Zero extension preserves scalar multiplication. -/
@[simp]
theorem extend_smul (c : ℂ) (f : boundedHolomorphicSections I F W) :
    extend (c • f) = c • extend f := by
  funext z
  by_cases hz : z ∈ W
  · simp [extend_apply_of_mem, hz]
  · simp [extend_apply_of_notMem, hz]

/-- The zero extension is holomorphic on `W`. -/
theorem mdifferentiableOn_extend (f : boundedHolomorphicSections I F W) :
    MDifferentiableOn I 𝓘(ℂ, F) (extend f) W :=
  mem_boundedHolomorphicSections_iff_extend.mp f.property

/-- Bundling the zero extension recovers the original map, for any valid bound. -/
@[simp]
theorem of_extend (f : boundedHolomorphicSections I F W)
    (hg : MDifferentiableOn I 𝓘(ℂ, F) (extend f) W) (C : ℝ)
    (hC : ∀ z ∈ W, ‖extend f z‖ ≤ C) : of W (extend f) hg C hC = f :=
  ext fun z => by simp

/-- The zero extension is bounded everywhere by the supremum norm. -/
theorem norm_extend_apply_le (f : boundedHolomorphicSections I F W) (z : X) :
    ‖extend f z‖ ≤ ‖f‖ := by
  by_cases hz : z ∈ W
  · rw [extend_apply f ⟨z, hz⟩]
    exact norm_coe_le_norm (f : W →ᵇ F) ⟨z, hz⟩
  · rw [extend_apply_of_notMem f hz, norm_zero]
    exact norm_nonneg _

/-- Restriction of bounded holomorphic maps to a smaller open set. -/
noncomputable def restrict (h : W' ≤ W) :
    boundedHolomorphicSections I F W →L[ℂ] boundedHolomorphicSections I F W' :=
  ((compContinuousCLM F ℂ ⟨fun z => ⟨z, h z.2⟩, continuous_subtype_val.subtype_mk _⟩).comp
    (boundedHolomorphicSections I F W).subtypeL).codRestrict _ fun f => by
    exact ⟨extend f, (mdifferentiableOn_extend f).mono h, fun z => extend_apply f ⟨z, h z.2⟩⟩

@[simp]
theorem restrict_apply (h : W' ≤ W) (f : boundedHolomorphicSections I F W) (z : W') :
    (restrict h f : W' →ᵇ F) z = (f : W →ᵇ F) ⟨z, h z.2⟩ := (rfl)

/-- Restriction agrees with restricting the same ambient representative. -/
@[simp]
theorem restrict_of (h : W' ≤ W) (g : X → F) (hg : MDifferentiableOn I 𝓘(ℂ, F) g W) (C : ℝ)
    (hC : ∀ z ∈ W, ‖g z‖ ≤ C) :
    restrict h (of W g hg C hC) = of W' g (hg.mono h) C fun z hz => hC z (h hz) :=
  ext fun z => by simp

/-- Restriction of an intrinsically defined map is its composition with the inclusion. -/
@[simp]
theorem restrict_ofMDifferentiable (h : W' ≤ W) (g : W → F)
    (hg : MDifferentiable I 𝓘(ℂ, F) g) (C : ℝ) (hC : ∀ z, ‖g z‖ ≤ C) :
    restrict h (ofMDifferentiable g hg C hC) =
      ofMDifferentiable (g ∘ Opens.inclusion h)
        (fun z => (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_inclusion h g z).mp
          (hg (Opens.inclusion h z))) C (fun z => hC (Opens.inclusion h z)) :=
  ext fun _ => rfl

/-- Restriction does not increase the supremum norm. -/
theorem norm_restrict_apply_le (h : W' ≤ W) (f : boundedHolomorphicSections I F W) :
    ‖restrict h f‖ ≤ ‖f‖ :=
  norm_compContinuous_le (f : W →ᵇ F) _

/-- Restriction has operator norm at most one. -/
theorem norm_restrict_le (h : W' ≤ W) : ‖restrict (I := I) (F := F) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa using norm_restrict_apply_le h f

/-- Restriction to the same open set is the identity. -/
@[simp]
theorem restrict_refl : restrict (I := I) (F := F) (le_refl W) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun _ => ext fun _ => rfl

/-- Restrictions compose. -/
@[simp]
theorem restrict_comp_restrict (h : W' ≤ W) (h' : W'' ≤ W') :
    (restrict (I := I) (F := F) h').comp (restrict h) = restrict (h'.trans h) :=
  ContinuousLinearMap.ext fun _ => ext fun _ => rfl

/-- Successive restrictions agree with restriction along the composite inclusion. -/
@[simp]
theorem restrict_restrict (h : W' ≤ W) (h' : W'' ≤ W')
    (f : boundedHolomorphicSections I F W) :
    restrict h' (restrict h f) = restrict (h'.trans h) f :=
  ext fun _ => rfl

variable [IsManifold I 1 X]

/-- **Cauchy estimate in a chart.** If the ball of radius `R` around `x`, read in the extended
chart `φ` at `x`, is mapped by the inverse chart into `W`, then a bounded holomorphic map `f` on
`W` satisfies `dist (f z) (f x) ≤ 2 * ‖f‖ / R * dist (φ z) (φ x)` for every `z` in the chart
source with `φ z` in that ball. -/
theorem dist_apply_le_of_ball_subset (f : boundedHolomorphicSections I F W) {x z : W} {R : ℝ}
    (hR : ball (extChartAt I (x : X) x) R ⊆
      (extChartAt I (x : X)).target ∩ (extChartAt I (x : X)).symm ⁻¹' W)
    (hzs : (z : X) ∈ (extChartAt I (x : X)).source)
    (hz : extChartAt I (x : X) z ∈ ball (extChartAt I (x : X) x) R) :
    dist ((f : W →ᵇ F) z) ((f : W →ᵇ F) x) ≤
      2 * ‖f‖ / R * dist (extChartAt I (x : X) z) (extChartAt I (x : X) x) := by
  set φ := extChartAt I (x : X)
  have hc : φ x ∈ ball (φ x) R := mem_ball_self (dist_nonneg.trans_lt hz)
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    (((mdifferentiableOn_extend f).differentiableOn_comp_extChartAt_symm (x : X)).mono hR)
    (mapsTo_closedBall_of_forall_norm_le (fun y _ => norm_extend_apply_le f _) hc) hz
  rwa [Function.comp_apply, Function.comp_apply, φ.left_inv hzs,
    φ.left_inv (mem_extChartAt_source (x : X)), extend_apply, extend_apply] at h

variable [I.Boundaryless] [ProperSpace F]

/-- **Montel's theorem for bounded holomorphic maps on a complex manifold.** If `W'` lies in a
compact subset `K` of `W` and `F` is proper, restriction `H^∞(W, F) → H^∞(W', F)` is a compact
operator. -/
theorem isCompactOperator_restrict {K : Set X} (hK : IsCompact K) (hW'K : (W' : Set X) ⊆ K)
    (hKW : K ⊆ W) :
    IsCompactOperator
      (restrict (I := I) (F := F) (SetLike.coe_subset_coe.mp (hW'K.trans hKW))) := by
  -- The unit ball of `H^∞(W, F)` is equicontinuous by the Cauchy estimate
  -- `dist_apply_le_of_ball_subset` in charts, so the Arzelà–Ascoli theorem applies on `K`.
  refine isCompactOperator_of_equicontinuousOn (isClosed_boundedHolomorphicSections W')
    (K := (↑) ⁻¹' K) ?_ ⟨fun z => ⟨z, hKW (hW'K z.2)⟩, continuous_subtype_val.subtype_mk _⟩
    (fun z => hW'K z.2) (restrict_apply _) fun x _ => EquicontinuousAt.equicontinuousWithinAt ?_ _
  · rwa [Subtype.isCompact_iff, image_preimage_eq_of_subset fun x hx => ⟨⟨x, hKW hx⟩, rfl⟩]
  · -- In the extended chart `φ` at `x`, on a ball of radius `R` mapped into `W`, the Cauchy
    -- estimate gives the common modulus `2 / R * dist (φ z) (φ x)`.
    set φ := extChartAt I (x : X)
    obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp
      ((continuousOn_extChartAt_symm (x : X)).isOpen_inter_preimage
        (isOpen_extChartAt_target (x : X)) W.isOpen)
      (φ x) ⟨mem_extChartAt_target (x : X), by simp [φ]⟩
    have hφ : ContinuousAt (fun z : W => φ z) x :=
      (continuousAt_extChartAt (x : X)).comp continuousAt_subtype_val
    refine equicontinuousAt_of_continuity_modulus (fun z : W => 2 / R * dist (φ z) (φ x)) ?_ _ ?_
    · have hc : Tendsto (fun z : W => 2 / R * dist (φ z) (φ x)) (𝓝 x)
          (𝓝 (2 / R * dist (φ x) (φ x))) :=
        (hφ.tendsto.dist tendsto_const_nhds).const_mul _
      simpa using hc
    · filter_upwards [continuousAt_subtype_val.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := I) (x : X)),
        hφ.preimage_mem_nhds (ball_mem_nhds _ hR)] with z hzs hz
      rintro ⟨f, hf⟩
      rw [mem_closedBall_zero_iff] at hf
      rw [dist_comm]
      refine (dist_apply_le_of_ball_subset f hRO hzs hz).trans ?_
      gcongr
      linarith

/-- If `F` is proper, restriction to an open set with compact closure inside `W` is a compact
operator. -/
theorem isCompactOperator_restrict_of_isCompact_closure
    (hW' : IsCompact (closure (W' : Set X))) (hW'W : closure (W' : Set X) ⊆ W) :
    IsCompactOperator
      (restrict (I := I) (F := F) (SetLike.coe_subset_coe.mp (subset_closure.trans hW'W))) :=
  isCompactOperator_restrict hW' subset_closure hW'W

end BoundedHolomorphicSections

end TauCeti
