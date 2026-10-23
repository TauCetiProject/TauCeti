/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.ZMultiples
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.PullbackGroupoid

/-!
# The circle `AddCircle p` as a smooth manifold

For a positive real `p`, the circle `AddCircle p = ℝ ⧸ pℤ` is the orbit space of the action of
`Multiplicative ℤ` on the real line by `n • t = t + n p`. This action is free and properly
discontinuous and acts by analytic maps, so `TauCeti.instIsManifoldQuotient` makes its orbit space
an analytic manifold modelled on `ℝ`. This file transports that structure to Mathlib's
topological circle `AddCircle p`, along the homeomorphism of the orbit space with `AddCircle p`.
The quotient map `((↑) : ℝ → AddCircle p)` is then an analytic local diffeomorphism; it is a
covering map by Mathlib's `AddCircle.isCoveringMap_coe`.

So that `ℝ` itself does not acquire a `p`-dependent action of `Multiplicative ℤ`, the action lives
on the type synonym `TauCeti.PeriodLine p` of `ℝ`, which carries the topology and the manifold
structure of `ℝ`. The equivalence `TauCeti.PeriodLine.ofReal p` identifies `ℝ` with it.

The charts of `AddCircle p` are local lifts to `ℝ`: every chart `c` of the atlas satisfies
`(c x : AddCircle p) = x` on its source (`AddCircle.coe_apply_of_mem_atlas`).

## Main definitions

* `TauCeti.PeriodLine p`: the real line, with the action of `Multiplicative ℤ` by translations
  by integer multiples of `p`.
* `TauCeti.PeriodLine.quotientHomeomorph p`: the homeomorphism of the orbit space of this action
  with `AddCircle p`.
* `AddCircle.instChartedSpace`, `AddCircle.instIsManifold`: the charts of `AddCircle p`, and the
  analytic manifold structure they form.
* `TauCeti.PeriodLine.quotientDiffeomorph p n`: the orbit space is diffeomorphic to
  `AddCircle p`.

## Main results

* `TauCeti.PeriodLine.instProperlyDiscontinuousSMul`, `TauCeti.PeriodLine.instIsCancelSMul`,
  `TauCeti.PeriodLine.instContMDiffConstSMul`: the action is properly discontinuous, free and by
  analytic maps.
* `AddCircle.isLocalDiffeomorph_coe`: the quotient map `ℝ → AddCircle p` is an analytic local
  diffeomorphism.
* `AddCircle.coe_apply_of_mem_atlas`: the charts of `AddCircle p` are local lifts to `ℝ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The real line, as the covering space of the circle `AddCircle p`: a type synonym of `ℝ`
carrying the action of `Multiplicative ℤ` by translations by integer multiples of `p`. -/
@[expose] def PeriodLine (_p : ℝ) : Type := ℝ

namespace PeriodLine

variable (p : ℝ)

instance : TopologicalSpace (PeriodLine p) := inferInstanceAs (TopologicalSpace ℝ)

instance : T2Space (PeriodLine p) := inferInstanceAs (T2Space ℝ)

instance : LocallyCompactSpace (PeriodLine p) := inferInstanceAs (LocallyCompactSpace ℝ)

instance : ChartedSpace ℝ (PeriodLine p) := inferInstanceAs (ChartedSpace ℝ ℝ)

instance {n : ℕ∞ω} : IsManifold 𝓘(ℝ) n (PeriodLine p) := inferInstanceAs (IsManifold 𝓘(ℝ) n ℝ)

/-- The identification of the real line with `PeriodLine p`. -/
def ofReal : ℝ ≃ PeriodLine p := Equiv.refl ℝ

/-- The chart of `PeriodLine p` at any point is the identification with `ℝ`. -/
theorem chartAt_apply (s t : PeriodLine p) : chartAt ℝ s t = (ofReal p).symm t := (rfl)

/- `PeriodLine p` carries the topology and the manifold structure of `ℝ`, and `ofReal p` is the
identity of `ℝ`, so its regularity is that of the identity map. -/

/-- The identification of the real line with `PeriodLine p` is continuous. -/
theorem continuous_ofReal : Continuous (ofReal p) := continuous_id

/-- The identification of `PeriodLine p` with the real line is continuous. -/
theorem continuous_ofReal_symm : Continuous (ofReal p).symm := continuous_id

/-- The identification of the real line with `PeriodLine p` is analytic. -/
theorem contMDiff_ofReal (n : ℕ∞ω) : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n (ofReal p) := contMDiff_id

/-- The identification of `PeriodLine p` with the real line is analytic. -/
theorem contMDiff_ofReal_symm (n : ℕ∞ω) : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n (ofReal p).symm := contMDiff_id

/-- The identification of the real line with `PeriodLine p` is a local diffeomorphism. -/
theorem isLocalDiffeomorph_ofReal (n : ℕ∞ω) : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) n (ofReal p) :=
  Diffeomorph.isLocalDiffeomorph
    { toEquiv := ofReal p
      contMDiff_toFun := contMDiff_ofReal p n
      contMDiff_invFun := contMDiff_ofReal_symm p n }

/-! ### The action of `Multiplicative ℤ` -/

instance : SMul (Multiplicative ℤ) (PeriodLine p) where
  smul n t := ofReal p ((ofReal p).symm t + n.toAdd • p)

/-- The integer `n` acts on `PeriodLine p` by translation by `n • p`. -/
theorem smul_def (n : Multiplicative ℤ) (t : PeriodLine p) :
    n • t = ofReal p ((ofReal p).symm t + n.toAdd • p) := (rfl)

/-- The integer `n` acts on `PeriodLine p` by translation by `n • p`, read in `ℝ`. -/
@[simp]
theorem ofReal_symm_smul (n : Multiplicative ℤ) (t : PeriodLine p) :
    (ofReal p).symm (n • t) = (ofReal p).symm t + n.toAdd • p := (rfl)

/-- The integer `n` acts on `PeriodLine p` by translation by `n • p`, read in `ℝ`. -/
@[simp]
theorem smul_ofReal (n : Multiplicative ℤ) (t : ℝ) :
    n • ofReal p t = ofReal p (t + n.toAdd • p) := (rfl)

/-- `Multiplicative ℤ` acts on the real line by translations by integer multiples of `p`. -/
instance : MulAction (Multiplicative ℤ) (PeriodLine p) where
  one_smul t := by simp [smul_def]
  mul_smul m n t := by simp [smul_def]; ring

/-- The action is jointly continuous. -/
instance : ContinuousSMul (Multiplicative ℤ) (PeriodLine p) where
  continuous_smul := by
    simp_rw [smul_def]
    exact (continuous_ofReal p).comp (((continuous_ofReal_symm p).comp continuous_snd).add
      ((continuous_of_discreteTopology (f := fun n : Multiplicative ℤ ↦ n.toAdd • p)).comp
        continuous_fst))

/-- The action is by analytic maps. -/
instance instContMDiffConstSMul {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ) n (Multiplicative ℤ) (PeriodLine p) where
  contMDiff_const_smul m := by
    simp_rw [smul_def]
    exact (contMDiff_ofReal p n).comp
      ((contMDiff_id.add contMDiff_const).comp (contMDiff_ofReal_symm p n))

/-! ### The orbit space -/

/-- Two points of `PeriodLine p` lie in one orbit exactly when the real numbers they represent have
the same image in `AddCircle p`. -/
theorem orbitRel_iff {s t : PeriodLine p} :
    MulAction.orbitRel (Multiplicative ℤ) (PeriodLine p) s t ↔
      ((ofReal p).symm s : AddCircle p) = (ofReal p).symm t := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, QuotientAddGroup.eq,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨-n.toAdd, by simp [neg_smul]⟩
  · rintro ⟨k, hk⟩
    refine ⟨Multiplicative.ofAdd (-k), (ofReal p).symm.injective ?_⟩
    simp only [ofReal_symm_smul, toAdd_ofAdd, neg_smul, hk]
    abel

/-- The orbit space of the action of `Multiplicative ℤ` on `PeriodLine p` is homeomorphic to
`AddCircle p`. -/
def quotientHomeomorph :
    MulAction.orbitRel.Quotient (Multiplicative ℤ) (PeriodLine p) ≃ₜ AddCircle p :=
  Homeomorph.Quotient.congr
    { toEquiv := (ofReal p).symm
      continuous_toFun := continuous_ofReal_symm p
      continuous_invFun := continuous_ofReal p }
    fun _ _ ↦ (orbitRel_iff p).trans Quotient.eq

/-- The orbit of `t` corresponds to the image of `t` in `AddCircle p`. -/
@[simp]
theorem quotientHomeomorph_mk (t : PeriodLine p) :
    quotientHomeomorph p (Quotient.mk _ t) = ((ofReal p).symm t : AddCircle p) := (rfl)

/-- The image of `t` in `AddCircle p` corresponds to the orbit of `t`. -/
@[simp]
theorem quotientHomeomorph_symm_coe (t : ℝ) :
    (quotientHomeomorph p).symm (t : AddCircle p) = Quotient.mk _ (ofReal p t) := (rfl)

variable [hp : Fact (0 < p)]

/-- For positive `p`, the action is free: a translation by a nonzero multiple of `p` has no fixed
point. -/
instance instIsCancelSMul : IsCancelSMul (Multiplicative ℤ) (PeriodLine p) where
  left_cancel' n s t h := by
    simpa using congrArg (ofReal p).symm h
  right_cancel' m n t h := by
    have h' : m.toAdd • p = n.toAdd • p := by simpa using congrArg (ofReal p).symm h
    exact Multiplicative.toAdd.injective (smul_left_injective ℤ hp.out.ne' h')

/-- For positive `p`, the action is properly discontinuous: only finitely many integers translate a
compact set to meet another compact set. -/
instance instProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul (Multiplicative ℤ) (PeriodLine p) where
  finite_disjoint_inter_image {K L} hK hL := by
    -- If `n • t ∈ L` for some `t ∈ K`, then `n • p` is the difference of a point of `L` and a
    -- point of `K`, which lies in a compact set.
    have hC : IsCompact ((fun x ↦ (ofReal p).symm x.1 - (ofReal p).symm x.2) '' L ×ˢ K) :=
      (hL.prod hK).image
        (((continuous_ofReal_symm p).comp continuous_fst).sub
          ((continuous_ofReal_symm p).comp continuous_snd))
    have hfin := tendsto_cofinite_cocompact_iff.mp
      (Int.tendsto_zmultiplesHom_cofinite hp.out.ne') _ hC
    refine (hfin.preimage Multiplicative.toAdd.injective.injOn).subset fun n hn ↦ ?_
    obtain ⟨_, ⟨t, ht, rfl⟩, hnt⟩ := hn
    exact ⟨(n • t, t), ⟨hnt, ht⟩, by simp⟩

end PeriodLine

end TauCeti

/-! ### The manifold structure of `AddCircle p` -/

namespace AddCircle

open TauCeti PeriodLine

variable (p : ℝ) [Fact (0 < p)]

/-- The charts of `AddCircle p`, transported from the orbit space of the action of
`Multiplicative ℤ` on `PeriodLine p` along `TauCeti.PeriodLine.quotientHomeomorph p`. -/
noncomputable instance instChartedSpace : ChartedSpace ℝ (AddCircle p) :=
  (quotientHomeomorph p).symm.pullbackChartedSpace

/-- The circle `AddCircle p` is an analytic manifold modelled on `ℝ`. -/
instance instIsManifold {n : ℕ∞ω} : IsManifold 𝓘(ℝ) n (AddCircle p) :=
  (quotientHomeomorph p).symm.pullback_isManifold 𝓘(ℝ) n

end AddCircle

namespace TauCeti.PeriodLine

variable (p : ℝ) [Fact (0 < p)]

/-- The orbit space of the action of `Multiplicative ℤ` on `PeriodLine p` is diffeomorphic to
`AddCircle p`. -/
noncomputable def quotientDiffeomorph (n : ℕ∞ω) :
    MulAction.orbitRel.Quotient (Multiplicative ℤ) (PeriodLine p) ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯
      AddCircle p :=
  ((quotientHomeomorph p).symm.pullbackDiffeomorph 𝓘(ℝ) n).symm

/-- The underlying map of `quotientDiffeomorph p n` is `quotientHomeomorph p`. -/
@[simp]
theorem coe_quotientDiffeomorph (n : ℕ∞ω) :
    ⇑(quotientDiffeomorph p n) = quotientHomeomorph p := by
  simp [quotientDiffeomorph]

/-- The underlying map of the inverse of `quotientDiffeomorph p n` is the inverse of
`quotientHomeomorph p`. -/
@[simp]
theorem coe_quotientDiffeomorph_symm (n : ℕ∞ω) :
    ⇑(quotientDiffeomorph p n).symm = (quotientHomeomorph p).symm :=
  (quotientHomeomorph p).symm.coe_pullbackDiffeomorph 𝓘(ℝ) n

end TauCeti.PeriodLine

namespace AddCircle

open TauCeti PeriodLine

variable (p : ℝ) [Fact (0 < p)]

/-- The quotient map `ℝ → AddCircle p` is an analytic local diffeomorphism. -/
theorem isLocalDiffeomorph_coe (n : ℕ∞ω) :
    IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) n ((↑) : ℝ → AddCircle p) := by
  have h : ((↑) : ℝ → AddCircle p) =
      quotientDiffeomorph p n ∘ Quotient.mk _ ∘ ofReal p := by
    funext t
    simp
  rw [h]
  intro t
  have h₁ := isLocalDiffeomorph_ofReal p n t
  have h₂ : IsLocalDiffeomorph 𝓘(ℝ) 𝓘(ℝ) n
      (Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (PeriodLine p))) :=
    isLocalDiffeomorph_quotientMk
  exact h₁.comp _ _ ((h₂ _).comp _ _ ((quotientDiffeomorph p n).isLocalDiffeomorph _))

/-- The quotient map `ℝ → AddCircle p` is analytic. -/
theorem contMDiff_coe (n : ℕ∞ω) : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n ((↑) : ℝ → AddCircle p) :=
  (isLocalDiffeomorph_coe p n).contMDiff

variable {p} in
/-- The charts of `AddCircle p` are local lifts to `ℝ`: a chart sends each point of its source to
a real number representing it. -/
theorem coe_apply_of_mem_atlas {c : OpenPartialHomeomorph (AddCircle p) ℝ}
    (hc : c ∈ atlas ℝ (AddCircle p)) {x : AddCircle p} (hx : x ∈ c.source) :
    (c x : AddCircle p) = x := by
  rw [Homeomorph.pullbackChartedSpace_atlas] at hc
  -- A chart of the orbit space is a local section of the orbit projection followed by a chart of
  -- `PeriodLine p`.
  obtain ⟨_, hc, rfl⟩ := hc
  obtain ⟨s, z, rfl, hs⟩ := exists_trans_eq_of_mem_atlas_quotient hc
  rw [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
    OpenPartialHomeomorph.trans_source] at hx
  -- The orbit projection undoes the local section, so `quotientHomeomorph p` sends the lifted point
  -- back to `x`.
  have h := congrArg (quotientHomeomorph p) (hs _ hx.1)
  simp only [quotientHomeomorph_mk, Homeomorph.apply_symm_apply] at h
  simp only [Homeomorph.transOpenPartialHomeomorph_apply, OpenPartialHomeomorph.coe_trans,
    Function.comp_apply, chartAt_apply]
  exact h

variable {p} in
/-- A local lift of `AddCircle p` to `ℝ`, a partial homeomorphism sending each point of its source
to a real number representing it, is a chart of the maximal atlas of `AddCircle p`. -/
theorem mem_maximalAtlas_of_coe_apply {n : ℕ∞ω} {c : OpenPartialHomeomorph (AddCircle p) ℝ}
    (hc : ∀ x ∈ c.source, (c x : AddCircle p) = x) :
    c ∈ IsManifold.maximalAtlas 𝓘(ℝ) n (AddCircle p) := by
  -- The inverse of a local lift is the restriction of the quotient map.
  have hsymm : ∀ u ∈ c.target, c.symm u = (u : AddCircle p) := fun u hu ↦ by
    rw [← hc _ (c.map_target hu), c.right_inv hu]
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  exact ⟨ContMDiffOn.of_comp_isLocalDiffeomorph (isLocalDiffeomorph_coe p n) c.continuousOn
      (contMDiffOn_id.congr fun x hx ↦ hc x hx),
    (contMDiff_coe p n).contMDiffOn.congr hsymm⟩

variable {p} in
/-- Two local lifts of `AddCircle p` to `ℝ` differ, near each point of their common source, by a
fixed integer multiple of `p`. -/
theorem exists_eventuallyEq_add_zsmul {c c' : OpenPartialHomeomorph (AddCircle p) ℝ}
    (hc : ∀ x ∈ c.source, (c x : AddCircle p) = x)
    (hc' : ∀ x ∈ c'.source, (c' x : AddCircle p) = x) {x : AddCircle p} (hx : x ∈ c.source)
    (hx' : x ∈ c'.source) :
    ∃ k : ℤ, c' =ᶠ[𝓝 x] fun y ↦ c y + k • p := by
  have hdiff : ∀ y ∈ c.source ∩ c'.source, ∃ k : ℤ, c' y - c y = k • p := fun y hy ↦ by
    have h : ((c y : ℝ) : AddCircle p) = c' y := by rw [hc y hy.1, hc' y hy.2]
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h)
    exact ⟨k, by rw [hk]; abel⟩
  obtain ⟨k, hk⟩ := hdiff x ⟨hx, hx'⟩
  refine ⟨k, ?_⟩
  -- The difference is continuous, so near `x` it stays within `p` of `k • p`, and the only
  -- multiple of `p` there is `k • p` itself.
  have hnear : ∀ᶠ y in 𝓝 x, |(c' y - c y) - k • p| < p := by
    have h : ContinuousAt (fun y ↦ c' y - c y) x := (c'.continuousAt hx').sub (c.continuousAt hx)
    filter_upwards [h.eventually (Metric.ball_mem_nhds _ (Fact.out : 0 < p))] with y hy
    rwa [Real.dist_eq, hk] at hy
  filter_upwards [c.open_source.mem_nhds hx, c'.open_source.mem_nhds hx', hnear]
    with y hy hy' hyk
  obtain ⟨m, hm⟩ := hdiff y ⟨hy, hy'⟩
  have hmk : |((m - k : ℤ) : ℝ)| < 1 := by
    rw [hm, ← sub_smul, zsmul_eq_mul, abs_mul, abs_of_pos (Fact.out : 0 < p)] at hyk
    exact (mul_lt_iff_lt_one_left (Fact.out : 0 < p)).mp hyk
  have hmk' : |m - k| < 1 := by exact_mod_cast hmk
  rw [← sub_eq_zero.mp (Int.abs_lt_one_iff.mp hmk'), ← hm]
  abel

end AddCircle
