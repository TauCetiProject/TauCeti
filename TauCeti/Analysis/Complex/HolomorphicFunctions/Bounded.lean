/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Sets.Opens
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Bounded holomorphic maps on an open set

For an open subset `U` of a complex normed space `V` and a complex normed space `E`,
`boundedHolomorphicFunctions E U` is the space `H^∞(U, E)` of bounded holomorphic maps
`U → E`, as a complex subspace of the bounded continuous maps `U →ᵇ E` with the supremum norm.
Holomorphy can be checked on any ambient representative `V → E`. An ambient map that is
holomorphic and bounded on `U` gives an element (`TauCeti.BoundedHolomorphicFunctions.of`), and
every element has the zero extension `TauCeti.BoundedHolomorphicFunctions.extend` as a canonical
ambient representative.

When `E` is complete, `H^∞(U, E)` is closed in `U →ᵇ E`
(`TauCeti.isClosed_boundedHolomorphicFunctions`), hence a Banach space. Restriction to a smaller
open set `U' ⊆ U` is a continuous linear map of norm at most one
(`TauCeti.BoundedHolomorphicFunctions.restrict`), and these maps are functorial. Holomorphic
germs along a compact set form the inductive limit of these Banach spaces over shrinking
neighbourhoods; the two further properties below say that its bonding maps are compact and
injective:

* **Compactness (Montel).** If `U'` lies in a compact subset of `U` and `E` is proper (for a
  complex normed space, finite-dimensional), restriction is a compact operator
  (`TauCeti.BoundedHolomorphicFunctions.isCompactOperator_restrict`).
* **Injectivity (identity theorem).** If `V` is finite-dimensional, `E` is complete, and every
  connected component of `U` meets `U'`, restriction is injective
  (`TauCeti.BoundedHolomorphicFunctions.restrict_injective`).

For `E` complete, the **point jets** `TauCeti.BoundedHolomorphicFunctions.iteratedLineDeriv`, the
`k`-th derivatives at `t = 0` of `t ↦ f (x + t • v)` for a point `x` of `U` and a direction `v`, are
continuous linear maps `H^∞(U, E) → E` by Cauchy's estimate
(`TauCeti.BoundedHolomorphicFunctions.norm_iteratedLineDeriv_apply_le`), and commute with
restriction. If all of them vanish at `x`, then `f` vanishes near `x`; consequently, if `V` is
finite-dimensional and every connected component of `U` meets `K`, the point jets at the points
of `K` separate `H^∞(U, E)`
(`TauCeti.BoundedHolomorphicFunctions.eq_zero_of_forall_iteratedLineDeriv_eq_zero`). Since they
only depend on the map near `x`, this is the input for the Hausdorff property of the inductive limit
of holomorphic germs along `K`.

## References

* J. Mujica, *Complex Analysis in Banach Spaces*, North-Holland Mathematics Studies **120**,
  North-Holland, 1986.
* G. Köthe, *Dualität in der Funktionentheorie*, J. Reine Angew. Math. **191** (1953), 30–49.
-/

public section

namespace TauCeti

open Filter Metric Set Topology TopologicalSpace BoundedContinuousFunction
open scoped ENNReal

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup E]
  [NormedSpace ℂ E]

variable (E) in
/-- The space `H^∞(U, E)` of bounded holomorphic maps on an open set `U` of a complex normed
space, as a subspace of the bounded continuous maps `U →ᵇ E` with the supremum norm. A bounded
continuous map belongs to it when some ambient map `V → E` agreeing with it on `U` is
holomorphic on `U`. -/
def boundedHolomorphicFunctions (U : Opens V) : Submodule ℂ (U →ᵇ E) where
  carrier := {f | ∃ g : V → E, DifferentiableOn ℂ g U ∧ ∀ z : U, g z = f z}
  zero_mem' := ⟨0, differentiableOn_const _, fun _ => rfl⟩
  add_mem' := by
    rintro f h ⟨g, hg, hgf⟩ ⟨k, hk, hkh⟩
    exact ⟨g + k, hg.add hk, fun z => by simp [hgf, hkh]⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hgf⟩
    exact ⟨c • g, hg.const_smul c, fun z => by simp [hgf]⟩

/-- Membership means having an ambient holomorphic representative. -/
theorem mem_boundedHolomorphicFunctions_iff {U : Opens V} {f : U →ᵇ E} :
    f ∈ boundedHolomorphicFunctions E U ↔
      ∃ g : V → E, DifferentiableOn ℂ g U ∧ ∀ z : U, g z = f z := Iff.rfl

/-- Holomorphy can be tested on any ambient map agreeing with `f` on `U`. -/
theorem mem_boundedHolomorphicFunctions_iff_of_eqOn {U : Opens V} {f : U →ᵇ E} {g : V → E}
    (hgf : ∀ z : U, g z = f z) :
    f ∈ boundedHolomorphicFunctions E U ↔ DifferentiableOn ℂ g U := by
  constructor
  · rintro ⟨k, hk, hkf⟩
    exact hk.congr fun z hz => (hgf ⟨z, hz⟩).trans (hkf ⟨z, hz⟩).symm
  · exact fun hg => ⟨g, hg, hgf⟩

/-- Equivalently, the extension by zero is holomorphic on `U`. -/
theorem mem_boundedHolomorphicFunctions_iff_extend {U : Opens V} {f : U →ᵇ E} :
    f ∈ boundedHolomorphicFunctions E U ↔
      DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ => 0)) U :=
  mem_boundedHolomorphicFunctions_iff_of_eqOn fun z =>
    Subtype.val_injective.extend_apply f (fun _ => 0) z

/-- For complete `E`, the bounded holomorphic maps form a closed subspace of the bounded
continuous maps: a uniform limit of holomorphic maps is holomorphic. -/
theorem isClosed_boundedHolomorphicFunctions [CompleteSpace E] (U : Opens V) :
    IsClosed (boundedHolomorphicFunctions E U : Set (U →ᵇ E)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hF, hFf⟩ := mem_closure_iff_seq_limit.mp hf
  choose G hG hGF using hF
  have hext : ∀ z : U, Function.extend Subtype.val f (fun _ => 0) z = f z :=
    Subtype.val_injective.extend_apply f (fun _ => 0)
  refine mem_boundedHolomorphicFunctions_iff_extend.mpr ?_
  refine TendstoUniformlyOn.differentiableOn (l := atTop) ?_ (Eventually.of_forall hG) U.isOpen
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hcomp : (Function.extend Subtype.val f (fun _ => 0) ∘ (↑) : U → E) = f := funext hext
  have hcoe : (fun n (z : U) => G n z) = fun n => ⇑(F n) := funext fun n => funext (hGF n)
  have hT := tendsto_iff_tendstoUniformly.mp hFf
  rw [← hcomp, ← hcoe] at hT
  exact hT

/-- For complete `E`, `H^∞(U, E)` is a Banach space. -/
instance [CompleteSpace E] (U : Opens V) : CompleteSpace (boundedHolomorphicFunctions E U) :=
  (isClosed_boundedHolomorphicFunctions U).completeSpace_coe

namespace BoundedHolomorphicFunctions

variable {U U' U'' : Opens V}

/-- Restrict an ambient map, holomorphic on `U` and bounded there by `C`, to an element of
`H^∞(U, E)`. -/
def of (U : Opens V) (g : V → E) (hg : DifferentiableOn ℂ g U) (C : ℝ)
    (hC : ∀ z ∈ U, ‖g z‖ ≤ C) : boundedHolomorphicFunctions E U :=
  ⟨.ofNormedAddCommGroup (fun z : U => g z) hg.continuousOn.domRestrict C fun z => hC z z.2,
    g, hg, fun _ => rfl⟩

@[simp]
theorem of_apply (g : V → E) (hg : DifferentiableOn ℂ g U) (C : ℝ) (hC : ∀ z ∈ U, ‖g z‖ ≤ C)
    (z : U) : (of U g hg C hC : U →ᵇ E) z = g z := (rfl)

/-- The ambient representative obtained by extending by zero. -/
noncomputable def extend (f : boundedHolomorphicFunctions E U) : V → E :=
  Function.extend Subtype.val (f : U →ᵇ E) (fun _ => 0)

@[simp]
theorem extend_apply (f : boundedHolomorphicFunctions E U) (z : U) :
    extend f z = (f : U →ᵇ E) z :=
  Subtype.val_injective.extend_apply _ _ _

/-- The zero extension vanishes outside `U`. -/
@[simp]
theorem extend_apply_of_notMem (f : boundedHolomorphicFunctions E U) {z : V} (hz : z ∉ U) :
    extend f z = 0 := by
  rw [extend, Function.extend_apply']
  rintro ⟨w, rfl⟩
  exact hz w.property

/-- The zero extension is holomorphic on `U`. -/
theorem differentiableOn_extend (f : boundedHolomorphicFunctions E U) :
    DifferentiableOn ℂ (extend f) U :=
  mem_boundedHolomorphicFunctions_iff_extend.mp f.property

/-- The zero extension is bounded everywhere by the supremum norm. -/
theorem norm_extend_apply_le (f : boundedHolomorphicFunctions E U) (z : V) :
    ‖extend f z‖ ≤ ‖f‖ := by
  by_cases hz : z ∈ U
  · rw [extend_apply f ⟨z, hz⟩]
    exact norm_coe_le_norm (f : U →ᵇ E) ⟨z, hz⟩
  · rw [extend_apply_of_notMem f hz, norm_zero]
    exact norm_nonneg _

/-- Bounded holomorphic functions on a finite-measure open set have an `Lᵖ` zero extension
for every exponent, including infinity. The range need not be complete or finite-dimensional. -/
theorem memLp_extend [MeasurableSpace V] [OpensMeasurableSpace V]
    [SecondCountableTopologyEither V E]
    {μ : MeasureTheory.Measure V} [MeasureTheory.IsFiniteMeasure (μ.restrict (U : Set V))]
    (p : ℝ≥0∞) (f : boundedHolomorphicFunctions E U) :
    MeasureTheory.MemLp (extend f) p (μ.restrict (U : Set V)) := by
  exact MeasureTheory.MemLp.of_bound
    ((differentiableOn_extend f).continuousOn.aestronglyMeasurable U.isOpen.measurableSet)
    ‖f‖ (Filter.Eventually.of_forall (norm_extend_apply_le f))

/-- Recovering a bounded holomorphic map from its zero extension does not change it. -/
@[simp]
theorem of_extend (f : boundedHolomorphicFunctions E U) :
    of U (extend f) (differentiableOn_extend f) ‖(f : U →ᵇ E)‖
      (fun z _ => (norm_extend_apply_le f z).trans_eq (Submodule.norm_coe f).symm) = f :=
  Subtype.ext (BoundedContinuousFunction.ext fun z => by simp)

/-- **Cauchy estimate.** On a ball of radius `R` inside `U`, a bounded holomorphic map `f` is
Lipschitz at the centre with constant `2 * ‖f‖ / R`. -/
theorem dist_apply_le_of_ball_subset (f : boundedHolomorphicFunctions E U) {x z : U} {R : ℝ}
    (hR : ball (x : V) R ⊆ U) (hz : dist z x < R) :
    dist ((f : U →ᵇ E) z) ((f : U →ᵇ E) x) ≤ 2 * ‖f‖ / R * dist z x := by
  rw [Subtype.dist_eq] at hz ⊢
  have hx : (x : V) ∈ ball (x : V) R := mem_ball_self (dist_nonneg.trans_lt hz)
  rw [← extend_apply f z, ← extend_apply f x]
  exact Complex.dist_le_div_mul_dist_of_mapsTo_ball ((differentiableOn_extend f).mono hR)
    (mapsTo_closedBall_of_forall_norm_le (fun y _ => norm_extend_apply_le f y) hx)
    (mem_ball.mpr hz)

/-- Restriction of bounded holomorphic maps to a smaller open set. -/
noncomputable def restrict (h : U' ≤ U) :
    boundedHolomorphicFunctions E U →L[ℂ] boundedHolomorphicFunctions E U' :=
  ((compContinuousCLM E ℂ ⟨fun z => ⟨z, h z.2⟩, continuous_subtype_val.subtype_mk _⟩).comp
    (boundedHolomorphicFunctions E U).subtypeL).codRestrict _ fun f => by
    exact ⟨extend f, (differentiableOn_extend f).mono h, fun z => extend_apply f ⟨z, h z.2⟩⟩

@[simp]
theorem restrict_apply (h : U' ≤ U) (f : boundedHolomorphicFunctions E U) (z : U') :
    (restrict h f : U' →ᵇ E) z = (f : U →ᵇ E) ⟨z, h z.2⟩ := (rfl)

/-- Restriction agrees with restricting the same ambient representative. -/
@[simp]
theorem restrict_of (h : U' ≤ U) (g : V → E) (hg : DifferentiableOn ℂ g U) (C : ℝ)
    (hC : ∀ z ∈ U, ‖g z‖ ≤ C) :
    restrict h (of U g hg C hC) = of U' g (hg.mono h) C fun z hz => hC z (h hz) :=
  Subtype.ext (BoundedContinuousFunction.ext fun z => by simp)

/-- Restriction does not increase the supremum norm. -/
theorem norm_restrict_apply_le (h : U' ≤ U) (f : boundedHolomorphicFunctions E U) :
    ‖restrict h f‖ ≤ ‖f‖ :=
  norm_compContinuous_le (f : U →ᵇ E) _

/-- Restriction has operator norm at most one. -/
theorem norm_restrict_le (h : U' ≤ U) : ‖restrict (E := E) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa using norm_restrict_apply_le h f

/-- Restriction to the same open set is the identity. -/
@[simp]
theorem restrict_refl : restrict (E := E) (le_refl U) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun _ => Subtype.ext (BoundedContinuousFunction.ext fun _ => rfl)

/-- Restrictions compose. -/
@[simp]
theorem restrict_comp_restrict (h : U' ≤ U) (h' : U'' ≤ U') :
    (restrict (E := E) h').comp (restrict h) = restrict (h'.trans h) :=
  ContinuousLinearMap.ext fun _ => Subtype.ext (BoundedContinuousFunction.ext fun _ => rfl)

/-- **Montel's theorem for bounded holomorphic maps.** If `U'` lies in a compact subset `K` of
`U` and `E` is proper, restriction `H^∞(U, E) → H^∞(U', E)` is a compact operator. -/
theorem isCompactOperator_restrict [ProperSpace E] {K : Set V} (hK : IsCompact K)
    (hU'K : (U' : Set V) ⊆ K) (hKU : K ⊆ U) :
    IsCompactOperator (restrict (E := E) (hU'K.trans hKU)) := by
  -- The unit ball of `H^∞(U, E)` is equicontinuous by the Cauchy estimate
  -- `dist_apply_le_of_ball_subset`, so the Arzelà–Ascoli theorem applies on the compact set `K`.
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ρ : C(K, U) := ⟨fun z => ⟨z, hKU z.2⟩, continuous_subtype_val.subtype_mk _⟩
  let σ : C(U', K) := ⟨fun z => ⟨z, hU'K z.2⟩, continuous_subtype_val.subtype_mk _⟩
  -- The unit ball of `H^∞(U, E)`, restricted to `K`.
  let A : Set (K →ᵇ E) :=
    (fun f : boundedHolomorphicFunctions E U => (f : U →ᵇ E).compContinuous ρ) '' closedBall 0 1
  have hA : IsCompact (closure A) := by
    refine arzela_ascoli (closedBall 0 1) (isCompact_closedBall 0 1) A ?_ ?_
    · rintro _ z ⟨f, hf, rfl⟩
      rw [mem_closedBall_zero_iff] at hf ⊢
      exact (norm_coe_le_norm (f : U →ᵇ E) _).trans hf
    · -- Equicontinuity at `x`: on a ball of radius `R` around `x` inside `U`, the Cauchy
      -- estimate gives the common modulus `2 / R * dist z x`.
      intro x
      obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp U.isOpen x (hKU x.2)
      refine equicontinuousAt_of_continuity_modulus (fun z : K => 2 / R * dist z x) ?_ _ ?_
      · have hc : Continuous fun z : K => 2 / R * dist z x := by fun_prop
        simpa using hc.tendsto x
      · filter_upwards [ball_mem_nhds x hR] with z hz
        rintro ⟨_, f, hf, rfl⟩
        rw [mem_closedBall_zero_iff] at hf
        rw [dist_comm]
        refine (dist_apply_le_of_ball_subset f (x := ρ x) (z := ρ z) hRU hz).trans ?_
        gcongr
        · linarith
        · exact le_rfl
  let S : (K →ᵇ E) → (U' →ᵇ E) := fun φ => φ.compContinuous σ
  have hcomp : IsCompact (((↑) : boundedHolomorphicFunctions E U' → U' →ᵇ E) ⁻¹'
      (S '' closure A)) :=
    (isClosed_boundedHolomorphicFunctions U').isClosedEmbedding_subtypeVal.isCompact_preimage
      (hA.image (continuous_compContinuous σ))
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
    ⟨closedBall 0 1, closedBall_mem_nhds _ one_pos, _, hcomp, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨_, subset_closure ⟨f, hf, rfl⟩,
    BoundedContinuousFunction.ext fun z => (restrict_apply (hU'K.trans hKU) f z).symm⟩

/-- If `E` is proper, restriction to an open set with compact closure inside `U` is a compact
operator. -/
theorem isCompactOperator_restrict_of_isCompact_closure [ProperSpace E]
    (hU' : IsCompact (closure (U' : Set V))) (hU'U : closure (U' : Set V) ⊆ U) :
    IsCompactOperator (restrict (E := E) (subset_closure.trans hU'U)) :=
  isCompactOperator_restrict hU' subset_closure hU'U

/-- **Identity theorem.** If `V` is finite-dimensional, `E` is complete, and every connected
component of `U` meets `U'`, then restriction `H^∞(U, E) → H^∞(U', E)` is injective. -/
theorem restrict_injective [FiniteDimensional ℂ V] [CompleteSpace E] (h : U' ≤ U)
    (hU' : ∀ x ∈ U, (connectedComponentIn (U : Set V) x ∩ U').Nonempty) :
    Function.Injective (restrict (E := E) h) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  have hg' := (differentiableOn_extend f).analyticOnNhd_of_finiteDimensional U.isOpen
  -- The zero extension of `f` vanishes on `U'`, hence near a point of `U'` in each component
  -- of `U`.
  have hzero : ∀ z ∈ U', extend f z = 0 := fun z hz => by
    rw [extend_apply f ⟨z, h hz⟩, ← restrict_apply h f ⟨z, hz⟩, hf]
    simp
  refine Subtype.ext (BoundedContinuousFunction.ext fun x => ?_)
  obtain ⟨y, hyx, hyU'⟩ := hU' x x.2
  have hev : extend f =ᶠ[𝓝 y] 0 :=
    eventually_of_mem (U'.isOpen.mem_nhds hyU') fun z hz => hzero z hz
  rw [← extend_apply f x]
  exact (hg'.mono (connectedComponentIn_subset _ _)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn hyx hev (mem_connectedComponentIn x.2)

/-- The zero extension of a sum is the sum of the zero extensions. -/
@[simp]
theorem extend_add (f g : boundedHolomorphicFunctions E U) :
    extend (f + g) = extend f + extend g := by
  funext z
  by_cases hz : z ∈ U
  · simp [extend_apply _ ⟨z, hz⟩]
  · simp [extend_apply_of_notMem _ hz]

/-- The zero extension of a scalar multiple is the scalar multiple of the zero extension. -/
@[simp]
theorem extend_smul (c : ℂ) (f : boundedHolomorphicFunctions E U) :
    extend (c • f) = c • extend f := by
  funext z
  by_cases hz : z ∈ U
  · simp [extend_apply _ ⟨z, hz⟩]
  · simp [extend_apply_of_notMem _ hz]

section IteratedLineDeriv

/-- The parameters `t` for which `x + t • v` lies in `U` form an open set. -/
private theorem isOpen_preimage_line (x v : V) :
    IsOpen ((fun t : ℂ => x + t • v) ⁻¹' (U : Set V)) :=
  U.isOpen.preimage (by fun_prop)

/-- On the complex line through `x` in the direction `v`, the zero extension of a bounded
holomorphic map is holomorphic wherever the line lies in `U`. -/
private theorem differentiableOn_extend_line (f : boundedHolomorphicFunctions E U) (x v : V) :
    DifferentiableOn ℂ (fun t : ℂ => extend f (x + t • v))
      ((fun t : ℂ => x + t • v) ⁻¹' (U : Set V)) :=
  (differentiableOn_extend f).comp
    ((by fun_prop : Differentiable ℂ fun t : ℂ => x + t • v).differentiableOn) fun _ ht => ht

variable [CompleteSpace E]

private theorem contDiffAt_extend_line (f : boundedHolomorphicFunctions E U) (x : U) (v : V)
    (k : ℕ) : ContDiffAt ℂ k (fun t : ℂ => extend f ((x : V) + t • v)) 0 :=
  ((differentiableOn_extend_line f x v).contDiffOn (isOpen_preimage_line (x : V) v)).contDiffAt
    ((isOpen_preimage_line (x : V) v).mem_nhds (by simp))

/-- Cauchy's estimate for the derivatives along the line through `x` in the direction `v`, when
the closed disc of parameters of radius `R` is mapped into `U`. -/
private theorem norm_iteratedDeriv_extend_line_le (f : boundedHolomorphicFunctions E U)
    {x v : V} (k : ℕ) {R : ℝ} (hR : 0 < R) (hRU : ∀ t : ℂ, ‖t‖ ≤ R → x + t • v ∈ U) :
    ‖iteratedDeriv k (fun t : ℂ => extend f (x + t • v)) 0‖ ≤ k.factorial * ‖f‖ / R ^ k := by
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR ?_
    fun _ _ => norm_extend_apply_le f _
  refine ((differentiableOn_extend_line f x v).mono fun t ht => hRU t ?_).diffContOnCl
  rwa [closure_ball _ hR.ne', mem_closedBall_zero_iff] at ht

/-- The derivative of order `k` at `x` in the direction `v`, as a linear map on `H^∞(U, E)`. -/
private noncomputable def iteratedLineDerivₗ (x : U) (v : V) (k : ℕ) :
    boundedHolomorphicFunctions E U →ₗ[ℂ] E where
  toFun f := iteratedDeriv k (fun t : ℂ => extend f ((x : V) + t • v)) 0
  map_add' f g := by
    simp only [extend_add, Pi.add_apply]
    exact iteratedDeriv_fun_add (contDiffAt_extend_line f x v k) (contDiffAt_extend_line g x v k)
  map_smul' c f := by
    simp only [extend_smul, Pi.smul_apply, RingHom.id_apply]
    exact iteratedDeriv_fun_const_smul_field c _

/-- **Point jets.** For a point `x` of `U`, a direction `v` and an order `k`, the `k`-th
derivative at `x` in the direction `v`, that is, the `k`-th derivative at `0` of
`t ↦ f (x + t • v)`, as a continuous linear map `H^∞(U, E) → E`. It is continuous by Cauchy's
estimate `norm_iteratedLineDeriv_apply_le`. -/
noncomputable def iteratedLineDeriv (x : U) (v : V) (k : ℕ) :
    boundedHolomorphicFunctions E U →L[ℂ] E :=
  (iteratedLineDerivₗ x v k).mkContinuousOfExistsBound <| by
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.1
      ((isOpen_preimage_line (U := U) (x : V) v).mem_nhds (x := 0) (by simp))
    refine ⟨k.factorial / R ^ k, fun f => ?_⟩
    rw [div_mul_eq_mul_div]
    exact norm_iteratedDeriv_extend_line_le f k hR fun t ht =>
      hRU (mem_closedBall_zero_iff.2 ht)

/-- The point jet of order `k` is the `k`-th derivative at `0` along the line `t ↦ x + t • v`. -/
theorem iteratedLineDeriv_apply (x : U) (v : V) (k : ℕ) (f : boundedHolomorphicFunctions E U) :
    iteratedLineDeriv x v k f = iteratedDeriv k (fun t : ℂ => extend f ((x : V) + t • v)) 0 :=
  (rfl)

/-- **Cauchy's estimate for point jets.** If `x + t • v ∈ U` whenever `‖t‖ ≤ R`, then the
derivative of order `k` at `x` in the direction `v` has norm at most `k! * ‖f‖ / R ^ k`. -/
theorem norm_iteratedLineDeriv_apply_le (x : U) (v : V) (k : ℕ) {R : ℝ} (hR : 0 < R)
    (hRU : ∀ t : ℂ, ‖t‖ ≤ R → (x : V) + t • v ∈ U) (f : boundedHolomorphicFunctions E U) :
    ‖iteratedLineDeriv x v k f‖ ≤ k.factorial * ‖f‖ / R ^ k :=
  norm_iteratedDeriv_extend_line_le f k hR hRU

/-- Point jets only depend on the map near the point: they commute with restriction. -/
@[simp]
theorem iteratedLineDeriv_restrict (h : U' ≤ U) (x : U') (v : V) (k : ℕ)
    (f : boundedHolomorphicFunctions E U) :
    iteratedLineDeriv x v k (restrict h f) = iteratedLineDeriv (⟨x, h x.2⟩ : U) v k f := by
  simp only [iteratedLineDeriv_apply]
  refine Filter.EventuallyEq.iteratedDeriv_eq k ?_
  filter_upwards [(isOpen_preimage_line (U := U') (x : V) v).mem_nhds (by simp)] with t ht
  rw [extend_apply (restrict h f) ⟨_, ht⟩, restrict_apply, extend_apply f ⟨_, h ht⟩]

/-- **Vanishing jets force local vanishing.** If all derivatives of all orders of `f` at `x` in
all directions vanish, then `f` vanishes near `x`. -/
theorem extend_eventuallyEq_zero_of_forall_iteratedLineDeriv_eq_zero (x : U)
    {f : boundedHolomorphicFunctions E U} (hf : ∀ v k, iteratedLineDeriv x v k f = 0) :
    extend f =ᶠ[𝓝 (x : V)] 0 := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp U.isOpen x x.2
  filter_upwards [ball_mem_nhds (x : V) hρ] with z hz
  set v := z - x
  have hv : ‖v‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hz
  -- Along the line `t ↦ x + t • v`, the parameter disc of radius `r > 1` lies in `ball x ρ`, and
  -- the Taylor series of `t ↦ f (x + t • v)` at `0` vanishes identically on it.
  set r := 2 * ρ / (‖v‖ + ρ)
  have hr : r * ‖v‖ < ρ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hρ (sub_pos.2 hv)]
  have hg : DifferentiableOn ℂ (fun t : ℂ => extend f (x + t • v)) (ball 0 r) := by
    refine (differentiableOn_extend_line f x v).mono fun t ht => hρU ?_
    rw [mem_ball_zero_iff] at ht
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht.le (norm_nonneg v)) hr
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, norm_one]
    exact (one_lt_div (by positivity)).2 (by linarith)
  have H := Complex.hasSum_taylorSeries_on_ball hg h1
  simp only [← iteratedLineDeriv_apply, hf, smul_zero] at H
  simpa [v] using H.unique hasSum_zero

/-- **Point jets along `K` separate bounded holomorphic maps.** If `V` is finite-dimensional and
every connected component of `U` meets `K`, then a bounded holomorphic map on `U` all of whose
derivatives of all orders, in all directions, vanish at every point of `K ∩ U` is zero. -/
theorem eq_zero_of_forall_iteratedLineDeriv_eq_zero [FiniteDimensional ℂ V] {K : Set V}
    (hK : ∀ x ∈ U, (connectedComponentIn (U : Set V) x ∩ K).Nonempty)
    {f : boundedHolomorphicFunctions E U}
    (hf : ∀ (x : U), (x : V) ∈ K → ∀ v k, iteratedLineDeriv x v k f = 0) : f = 0 := by
  -- `f` vanishes on the open set `U'` where its zero extension vanishes locally, which contains
  -- `K ∩ U`, so the identity theorem `restrict_injective` applies to the restriction to `U'`.
  let U' : Opens V := U ⊓ ⟨interior {z | extend f z = 0}, isOpen_interior⟩
  refine restrict_injective (E := E) (U' := U') inf_le_left (fun x hx => ?_) ?_
  · obtain ⟨y, hyx, hyK⟩ := hK x hx
    have hyU : y ∈ U := connectedComponentIn_subset _ _ hyx
    exact ⟨y, hyx, hyU, mem_interior_iff_mem_nhds.2
      (extend_eventuallyEq_zero_of_forall_iteratedLineDeriv_eq_zero ⟨y, hyU⟩ (hf _ hyK))⟩
  · refine Subtype.ext (BoundedContinuousFunction.ext fun z => ?_)
    rw [restrict_apply, ← extend_apply]
    exact interior_subset z.2.2

end IteratedLineDeriv

end BoundedHolomorphicFunctions

end TauCeti
