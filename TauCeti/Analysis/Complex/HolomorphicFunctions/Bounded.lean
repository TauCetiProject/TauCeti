/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.UniformLimit

/-!
# Bounded holomorphic maps on an open set

For an open subset `U` of a complex normed space `V` and a complex normed space `E`,
`boundedHolomorphicFunctions U E` is the space `H^∞(U, E)` of bounded holomorphic maps
`U → E`, as a complex subspace of the bounded continuous maps `U →ᵇ E` with the supremum norm.
Holomorphy can be checked on any ambient representative `V → E`.

When `E` is complete, `H^∞(U, E)` is closed in `U →ᵇ E`
(`TauCeti.isClosed_boundedHolomorphicFunctions`), hence a Banach space. Restriction to a smaller
open set `U' ⊆ U` is a continuous linear map of norm at most one
(`TauCeti.BoundedHolomorphicFunctions.restrict`), and these maps are functorial. Holomorphic
germs along a compact set form the inductive limit of these Banach spaces over shrinking
neighbourhoods; the two further properties below say that its bonding maps are compact and
injective:

* **Compactness (Montel).** If `U'` lies in a compact subset of `U` and `E` is proper (for a
  complex normed space, finite-dimensional), restriction is a compact operator
  (`TauCeti.BoundedHolomorphicFunctions.isCompactOperator_restrict`). The unit ball of `H^∞(U, E)`
  is equicontinuous by the Cauchy estimate
  `TauCeti.BoundedHolomorphicFunctions.dist_apply_le_of_ball_subset`, so the Arzelà–Ascoli theorem
  applies on the compact set.
* **Injectivity (identity theorem).** If `V` is finite-dimensional and every connected component
  of `U` meets `U'`, restriction is injective
  (`TauCeti.BoundedHolomorphicFunctions.restrict_injective`).

## References

* J. Mujica, *Complex Analysis in Banach Spaces*, North-Holland Mathematics Studies **120**,
  North-Holland, 1986.
* G. Köthe, *Dualität in der Funktionentheorie*, J. Reine Angew. Math. **191** (1953), 30–49.
-/

public section

namespace TauCeti

open Filter Metric Set Topology TopologicalSpace BoundedContinuousFunction

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

/-- For complete `E`, the bounded holomorphic maps form a closed subspace of the bounded
continuous maps: a uniform limit of holomorphic maps is holomorphic. -/
theorem isClosed_boundedHolomorphicFunctions [CompleteSpace E] (U : Opens V) :
    IsClosed (boundedHolomorphicFunctions E U : Set (U →ᵇ E)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hF, hFf⟩ := mem_closure_iff_seq_limit.mp hf
  choose G hG hGF using hF
  have hext : ∀ z : U, Function.extend Subtype.val f 0 z = f z :=
    Subtype.val_injective.extend_apply f 0
  refine (mem_boundedHolomorphicFunctions_iff_of_eqOn hext).mpr ?_
  refine TendstoUniformlyOn.differentiableOn (l := atTop) ?_ (Eventually.of_forall hG) U.isOpen
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hcomp : (Function.extend Subtype.val f 0 ∘ (↑) : U → E) = f := funext hext
  have hcoe : (fun n (z : U) => G n z) = fun n => ⇑(F n) := funext fun n => funext (hGF n)
  have hT := tendsto_iff_tendstoUniformly.mp hFf
  rw [← hcomp, ← hcoe] at hT
  exact hT

/-- For complete `E`, `H^∞(U, E)` is a Banach space. -/
instance [CompleteSpace E] (U : Opens V) : CompleteSpace (boundedHolomorphicFunctions E U) :=
  (isClosed_boundedHolomorphicFunctions U).completeSpace_coe

namespace BoundedHolomorphicFunctions

variable {U U' U'' : Opens V}

/-- **Cauchy estimate.** On a ball of radius `R` inside `U`, a bounded holomorphic map `f` is
Lipschitz at the centre with constant `2 * ‖f‖ / R`. -/
theorem dist_apply_le_of_ball_subset (f : boundedHolomorphicFunctions E U) {x z : U} {R : ℝ}
    (hR : ball (x : V) R ⊆ U) (hz : dist z x < R) :
    dist ((f : U →ᵇ E) z) ((f : U →ᵇ E) x) ≤ 2 * ‖f‖ / R * dist z x := by
  obtain ⟨g, hg, hgf⟩ := f.2
  have hbound : ∀ y (hy : y ∈ ball (x : V) R), ‖g y‖ ≤ ‖f‖ := fun y hy =>
    (hgf ⟨y, hR hy⟩).symm ▸ norm_coe_le_norm (f : U →ᵇ E) ⟨y, hR hy⟩
  have hx : (x : V) ∈ ball (x : V) R := mem_ball_self (dist_nonneg.trans_lt hz)
  rw [← hgf z, ← hgf x]
  refine Complex.dist_le_div_mul_dist_of_mapsTo_ball (hg.mono hR) (fun y hy => ?_) hz
  rw [mem_closedBall]
  linarith [dist_le_norm_add_norm (g y) (g x), hbound y hy, hbound x hx]

/-- Restriction of bounded holomorphic maps to a smaller open set. -/
noncomputable def restrict (h : U' ≤ U) :
    boundedHolomorphicFunctions E U →L[ℂ] boundedHolomorphicFunctions E U' :=
  ((compContinuousCLM E ℂ ⟨fun z => ⟨z, h z.2⟩, continuous_subtype_val.subtype_mk _⟩).comp
    (boundedHolomorphicFunctions E U).subtypeL).codRestrict _ fun f => by
    obtain ⟨g, hg, hgf⟩ := f.2
    exact ⟨g, hg.mono h, fun z => hgf ⟨z, h z.2⟩⟩

@[simp]
theorem restrict_apply (h : U' ≤ U) (f : boundedHolomorphicFunctions E U) (z : U') :
    (restrict h f : U' →ᵇ E) z = (f : U →ᵇ E) ⟨z, h z.2⟩ := (rfl)

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
  exact ⟨_, subset_closure ⟨f, hf, rfl⟩, rfl⟩

/-- Restriction to an open set with compact closure inside `U` is a compact operator. -/
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
  obtain ⟨g, hg, hgf⟩ := f.2
  have hg' := hg.analyticOnNhd_of_finiteDimensional U.isOpen
  -- `g` vanishes on `U'`, hence near a point of `U'` in each component of `U`.
  have hzero : ∀ z ∈ U', g z = 0 := fun z hz => by
    rw [hgf ⟨z, h hz⟩, ← restrict_apply h f ⟨z, hz⟩, hf]
    rfl
  refine Subtype.ext (BoundedContinuousFunction.ext fun x => ?_)
  obtain ⟨y, hyx, hyU'⟩ := hU' x x.2
  have hev : g =ᶠ[𝓝 y] 0 :=
    eventually_of_mem (U'.isOpen.mem_nhds hyU') fun z hz => hzero z hz
  rw [← hgf x]
  exact (hg'.mono (connectedComponentIn_subset _ _)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_connectedComponentIn hyx hev (mem_connectedComponentIn x.2)

end BoundedHolomorphicFunctions

end TauCeti
