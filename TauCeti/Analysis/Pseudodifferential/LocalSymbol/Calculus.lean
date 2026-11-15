/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Composition and derivatives of symbols on an open set of positions

For an open set `U ⊆ ℝⁿ`, the symbols of order `m` on `U × ℝⁿ` (`TauCeti.LocalSymbol`) are the
full symbols of pseudodifferential operators read in a chart. This file equips them with the
first operations of the symbol calculus, as `TauCeti.Analysis.Pseudodifferential.Symbol.Basic`
does for symbols on `ℝⁿ × ℝⁿ`:

* `TauCeti.LocalSymbol.comp`: the pointwise composition `b(x, ξ) ∘ a(x, ξ)` of symbols of orders
  `m'` and `m` is a symbol of order `m' + m` (the matrix product, for matrix-valued symbols);
* `TauCeti.LocalSymbol.spatialDeriv`: the position derivative `∂_{x_j} a` keeps the order `m`;
* `TauCeti.LocalSymbol.frequencyDeriv`: the frequency derivative `∂_{ξ_j} a` has order `m - 1`.

The derivatives satisfy the Leibniz rules for `comp` (`TauCeti.LocalSymbol.spatialDeriv_comp`,
`TauCeti.LocalSymbol.frequencyDeriv_comp`) and commute with each other, and composition is
bilinear and associative. All three operations commute with restriction to smaller open sets and
with restriction of symbols on `ℝⁿ` (`TauCeti.Symbol.restrict_comp`,
`TauCeti.Symbol.restrict_spatialDeriv`, `TauCeti.Symbol.restrict_frequencyDeriv`), so over `ℝⁿ`
they are the operations of `TauCeti.Symbol` (`TauCeti.Symbol.restrictTopEquiv_comp`,
`TauCeti.Symbol.restrictTopEquiv_spatialDeriv`, `TauCeti.Symbol.restrictTopEquiv_frequencyDeriv`).
For cutoffs `ψ` and `ψ'` with `ψ' = 1` on the support of `ψ`, the cut-off extensions satisfy
`ψ' b ∘ ψ a = ψ (b ∘ a)` (`TauCeti.LocalSymbol.extend_comp_extend`).

At positions outside `U` the coefficients are `0`, following the convention of
`TauCeti.LocalSymbol`; for the position derivative this is imposed by an indicator, since the
derivative of the extended coefficient at a boundary point need not vanish.

## Implementation notes

The constructions go through `TauCeti.LocalSymbol.ofEventuallyEq`. Near every position `x ∈ U` a
local symbol agrees with a symbol on `ℝⁿ`, namely its extension by a cutoff equal to `1` near `x`
(`TauCeti.LocalSymbol.exists_symbol_eventually_eq`), and the operations of `TauCeti.Symbol` applied
to such representatives agree near `x` with the local operations
(`TauCeti.LocalSymbol.eventually_coefficient_comp`,
`TauCeti.LocalSymbol.eventually_coefficient_spatialDeriv`,
`TauCeti.LocalSymbol.eventually_coefficient_frequencyDeriv`). The algebraic identities are proved
the same way, by transferring the corresponding identities for `TauCeti.Symbol` at each position.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.15).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.1.
-/

public section

noncomputable section

open scoped ContDiff Topology
open Set Filter

namespace TauCeti

variable {n : ℕ}

namespace LocalSymbol

variable {U U' : TopologicalSpace.Opens (CoordinateSpace n)} {V W X : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup X] [NormedSpace ℂ X] {m m' : ℝ} {x : CoordinateSpace n}

/-- Near every position of `U`, a local symbol agrees with a symbol on `ℝⁿ`: its extension by a
cutoff equal to `1` near the position. This is the converse of
`TauCeti.LocalSymbol.ofEventuallyEq`. -/
theorem exists_symbol_eventually_eq (a : LocalSymbol U V W m) (hx : x ∈ U) :
    ∃ s : Symbol n V W m, ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η) := by
  obtain ⟨ψ, hψ, -, hψ1, -, hψU⟩ := isCompact_singleton.exists_contDiff_cutoff_eventuallyEq_one
    U.isOpen (singleton_subset_iff.2 hx)
  refine ⟨extend ψ hψ hψU a, ?_⟩
  filter_upwards [hψ1 x rfl] with y hy η
  simp [hy]

section Comp

/-- The pointwise composition `(x, ξ) ↦ b(x, ξ) ∘ a(x, ξ)` of symbols of orders `m'` and `m` on
`U` is a symbol of order `m' + m` on `U`. For matrix-valued symbols this is the matrix product. -/
def comp (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) : LocalSymbol U V X (m' + m) :=
  ofEventuallyEq (fun p => (b.coefficient p).comp (a.coefficient p))
    (fun y hy η => by simp [a.coefficient_of_notMem y hy η])
    fun y hy => by
      obtain ⟨t, ht⟩ := b.exists_symbol_eventually_eq hy
      obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
      refine ⟨t.comp s, ?_⟩
      filter_upwards [ht, hs] with z hzt hzs η
      rw [Symbol.coefficient_comp, hzt η, hzs η]

@[simp]
theorem coefficient_comp (b : LocalSymbol U W X m') (a : LocalSymbol U V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (b.comp a).coefficient p = (b.coefficient p).comp (a.coefficient p) :=
  congrFun (coefficient_ofEventuallyEq _ _ _) p

/-- If symbols `t` and `s` on `ℝⁿ` agree near `x` with local symbols `b` and `a`, then `t ∘ s`
agrees near `x` with `b ∘ a`. -/
theorem eventually_coefficient_comp {b : LocalSymbol U W X m'} {a : LocalSymbol U V W m}
    {t : Symbol n W X m'} {s : Symbol n V W m}
    (ht : ∀ᶠ y in 𝓝 x, ∀ η, t.coefficient (y, η) = b.coefficient (y, η))
    (hs : ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η)) :
    ∀ᶠ y in 𝓝 x, ∀ η, (t.comp s).coefficient (y, η) = (b.comp a).coefficient (y, η) := by
  filter_upwards [ht, hs] with y hyt hys η
  rw [Symbol.coefficient_comp, coefficient_comp, hyt η, hys η]

theorem comp_add (b : LocalSymbol U W X m') (a₁ a₂ : LocalSymbol U V W m) :
    b.comp (a₁ + a₂) = b.comp a₁ + b.comp a₂ :=
  LocalSymbol.ext (funext fun p => by simp [ContinuousLinearMap.comp_add])

theorem add_comp (b₁ b₂ : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    (b₁ + b₂).comp a = b₁.comp a + b₂.comp a :=
  LocalSymbol.ext (funext fun p => by simp [ContinuousLinearMap.add_comp])

theorem comp_smul (c : ℂ) (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    b.comp (c • a) = c • b.comp a :=
  LocalSymbol.ext (funext fun p => by simp)

theorem smul_comp (c : ℂ) (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    (c • b).comp a = c • b.comp a :=
  LocalSymbol.ext (funext fun p => by simp [ContinuousLinearMap.smul_comp])

@[simp]
theorem comp_zero (b : LocalSymbol U W X m') : b.comp (0 : LocalSymbol U V W m) = 0 :=
  LocalSymbol.ext (funext fun p => by simp)

@[simp]
theorem zero_comp (a : LocalSymbol U V W m) : (0 : LocalSymbol U W X m').comp a = 0 :=
  LocalSymbol.ext (funext fun p => by simp)

@[simp]
theorem comp_neg (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    b.comp (-a) = -b.comp a :=
  LocalSymbol.ext (funext fun p => by simp)

@[simp]
theorem neg_comp (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    (-b).comp a = -b.comp a :=
  LocalSymbol.ext (funext fun p => by simp)

theorem comp_sub (b : LocalSymbol U W X m') (a₁ a₂ : LocalSymbol U V W m) :
    b.comp (a₁ - a₂) = b.comp a₁ - b.comp a₂ :=
  LocalSymbol.ext (funext fun p => by simp [ContinuousLinearMap.comp_sub])

theorem sub_comp (b₁ b₂ : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    (b₁ - b₂).comp a = b₁.comp a - b₂.comp a :=
  LocalSymbol.ext (funext fun p => by simp [ContinuousLinearMap.sub_comp])

theorem inclusion_comp {m'' : ℝ} (h : m' ≤ m'') (b : LocalSymbol U W X m')
    (a : LocalSymbol U V W m) :
    (inclusion h b).comp a = inclusion (by linarith) (b.comp a) :=
  LocalSymbol.ext (funext fun p => by simp)

theorem comp_inclusion {m'' : ℝ} (h : m ≤ m'') (b : LocalSymbol U W X m')
    (a : LocalSymbol U V W m) :
    b.comp (inclusion h a) = inclusion (by linarith) (b.comp a) :=
  LocalSymbol.ext (funext fun p => by simp)

/-- Composition of local symbols is associative, up to the identification of the orders
`(m'' + m') + m = m'' + (m' + m)`. -/
theorem comp_assoc {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] {m'' : ℝ}
    (c : LocalSymbol U X Y m'') (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    (c.comp b).comp a = inclusion (add_assoc m'' m' m).ge (c.comp (b.comp a)) :=
  LocalSymbol.ext (funext fun p => by simp [ContinuousLinearMap.comp_assoc])

/-- Restriction to a smaller open set commutes with composition. -/
@[simp]
theorem restrict_comp (h : U' ≤ U) (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    restrict h (b.comp a) = (restrict h b).comp (restrict h a) :=
  ext_of_mem fun y hy η => by simp [hy]

/-- For cutoffs `ψ` and `ψ'` with `ψ' = 1` on the support of `ψ`, the composition of the cut-off
extensions `ψ' b` and `ψ a` is the cut-off extension `ψ (b ∘ a)`. -/
theorem extend_comp_extend {ψ ψ' : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ U) (hψ' : ContDiff ℝ ∞ ψ') (hψ'U : tsupport ψ' ⊆ U)
    (hψψ' : EqOn ψ' 1 (tsupport ψ)) (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    (extend ψ' hψ' hψ'U b).comp (extend ψ hψ hψU a) = extend ψ hψ hψU (b.comp a) := by
  refine Symbol.ext (funext fun ⟨y, η⟩ => ?_)
  by_cases hy : y ∈ tsupport ψ
  · simp [(hψψ' hy).trans (Pi.one_apply y)]
  · simp [image_eq_zero_of_notMem_tsupport hy]

end Comp

section SpatialDeriv

/-- The coefficient of the position derivative `∂_{x_j} a` of a local symbol, cut off to `0` at
positions outside `U`. -/
private def spatialDerivCoeff (j : Fin n) (a : LocalSymbol U V W m) :
    CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
  ((U : Set (CoordinateSpace n)) ×ˢ univ).indicator
    fun p => coordinateDeriv [j] (fun y => a.coefficient (y, p.2)) p.1

private theorem spatialDerivCoeff_of_notMem (j : Fin n) (a : LocalSymbol U V W m) (hx : x ∉ U)
    (ξ : CoordinateSpace n) : spatialDerivCoeff j a (x, ξ) = 0 :=
  indicator_of_notMem (by simp [hx]) _

private theorem eventually_spatialDerivCoeff (j : Fin n) {a : LocalSymbol U V W m}
    {s : Symbol n V W m} (hx : x ∈ U)
    (hs : ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η)) :
    ∀ᶠ y in 𝓝 x, ∀ η,
      (Symbol.spatialDeriv j s).coefficient (y, η) = spatialDerivCoeff j a (y, η) := by
  filter_upwards [hs.eventually_nhds, U.isOpen.mem_nhds hx] with y hy hyU η
  rw [spatialDerivCoeff, indicator_of_mem (mk_mem_prod hyU (mem_univ η)),
    Symbol.coefficient_spatialDeriv]
  exact (Filter.EventuallyEq.coordinateDeriv (f := fun z => s.coefficient (z, η))
    (g := fun z => a.coefficient (z, η)) (hy.mono fun z hz => hz η) [j]).eq_of_nhds

/-- The position derivative of a local symbol, before bundling it as a linear map. -/
private def spatialDerivAux (j : Fin n) (a : LocalSymbol U V W m) : LocalSymbol U V W m :=
  ofEventuallyEq (spatialDerivCoeff j a) (fun _ hy η => spatialDerivCoeff_of_notMem j a hy η)
    fun y hy => by
      obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
      exact ⟨Symbol.spatialDeriv j s, eventually_spatialDerivCoeff j hy hs⟩

private theorem eventually_coefficient_spatialDerivAux (j : Fin n) {a : LocalSymbol U V W m}
    {s : Symbol n V W m} (hx : x ∈ U)
    (hs : ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η)) :
    ∀ᶠ y in 𝓝 x, ∀ η,
      (Symbol.spatialDeriv j s).coefficient (y, η) = (spatialDerivAux j a).coefficient (y, η) := by
  rw [spatialDerivAux, coefficient_ofEventuallyEq]
  exact eventually_spatialDerivCoeff j hx hs

/-- The position derivative `∂_{x_j} a` of a symbol of order `m` on `U`, again a symbol of order
`m` on `U`. Its coefficient is `0` at positions outside `U`. -/
def spatialDeriv (j : Fin n) : LocalSymbol U V W m →ₗ[ℂ] LocalSymbol U V W m where
  toFun := spatialDerivAux j
  map_add' a b := ext_of_mem fun y hy η => by
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    obtain ⟨t, ht⟩ := b.exists_symbol_eventually_eq hy
    have hst : ∀ᶠ z in 𝓝 y, ∀ η, (s + t).coefficient (z, η) = (a + b).coefficient (z, η) := by
      filter_upwards [hs, ht] with z hzs hzt η
      simp [hzs η, hzt η]
    rw [← (eventually_coefficient_spatialDerivAux j hy hst).self_of_nhds η, map_add,
      Symbol.coefficient_add, Pi.add_apply, coefficient_add, Pi.add_apply,
      (eventually_coefficient_spatialDerivAux j hy hs).self_of_nhds η,
      (eventually_coefficient_spatialDerivAux j hy ht).self_of_nhds η]
  map_smul' c a := ext_of_mem fun y hy η => by
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    have hcs : ∀ᶠ z in 𝓝 y, ∀ η, (c • s).coefficient (z, η) = (c • a).coefficient (z, η) := by
      filter_upwards [hs] with z hzs η
      simp [hzs η]
    rw [← (eventually_coefficient_spatialDerivAux j hy hcs).self_of_nhds η, map_smul,
      Symbol.coefficient_smul, Pi.smul_apply, RingHom.id_apply, coefficient_smul, Pi.smul_apply,
      (eventually_coefficient_spatialDerivAux j hy hs).self_of_nhds η]

/-- If a symbol `s` on `ℝⁿ` agrees near `x ∈ U` with a local symbol `a`, then `∂_{x_j} s` agrees
near `x` with `∂_{x_j} a`. -/
theorem eventually_coefficient_spatialDeriv (j : Fin n) {a : LocalSymbol U V W m}
    {s : Symbol n V W m} (hx : x ∈ U)
    (hs : ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η)) :
    ∀ᶠ y in 𝓝 x, ∀ η,
      (Symbol.spatialDeriv j s).coefficient (y, η) = (spatialDeriv j a).coefficient (y, η) :=
  eventually_coefficient_spatialDerivAux j hx hs

/-- At positions of `U`, the coefficient of `∂_{x_j} a` is the coordinate derivative of the
coefficient of `a`. -/
@[simp]
theorem coefficient_spatialDeriv_of_mem (j : Fin n) (a : LocalSymbol U V W m) (hx : x ∈ U)
    (ξ : CoordinateSpace n) :
    (spatialDeriv j a).coefficient (x, ξ) =
      coordinateDeriv [j] (fun y => a.coefficient (y, ξ)) x := by
  obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hx
  rw [← (eventually_coefficient_spatialDeriv j hx hs).self_of_nhds ξ]
  exact ((eventually_spatialDerivCoeff j hx hs).self_of_nhds ξ).trans
    (indicator_of_mem (mk_mem_prod hx (mem_univ ξ)) _)

@[simp]
theorem coefficient_spatialDeriv_of_notMem (j : Fin n) (a : LocalSymbol U V W m) (hx : x ∉ U)
    (ξ : CoordinateSpace n) : (spatialDeriv j a).coefficient (x, ξ) = 0 :=
  (spatialDeriv j a).coefficient_of_notMem x hx ξ

/-- At positions of `U`, the mixed derivatives of `∂_{x_j} a` are those of `a` with one more
position derivative. -/
theorem mixedDeriv_spatialDeriv (j : Fin n) (a : LocalSymbol U V W m) (hx : x ∈ U)
    (α β : List (Fin n)) (ξ : CoordinateSpace n) :
    mixedDeriv α β (spatialDeriv j a).coefficient x ξ =
      mixedDeriv (α ++ [j]) β a.coefficient x ξ := by
  obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hx
  rw [← mixedDeriv_congr_of_eventually (eventually_coefficient_spatialDeriv j hx hs),
    Symbol.mixedDeriv_spatialDeriv, mixedDeriv_congr_of_eventually hs]

/-- The Leibniz rule for a position derivative of a composition. -/
theorem spatialDeriv_comp (j : Fin n) (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    spatialDeriv j (b.comp a) = (spatialDeriv j b).comp a + b.comp (spatialDeriv j a) :=
  ext_of_mem fun y hy η => by
    obtain ⟨t, ht⟩ := b.exists_symbol_eventually_eq hy
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    have hts := eventually_coefficient_spatialDeriv j hy (eventually_coefficient_comp ht hs)
    rw [← hts.self_of_nhds η, Symbol.spatialDeriv_comp, Symbol.coefficient_add, Pi.add_apply,
      coefficient_add, Pi.add_apply,
      (eventually_coefficient_comp (eventually_coefficient_spatialDeriv j hy ht) hs).self_of_nhds η,
      (eventually_coefficient_comp ht (eventually_coefficient_spatialDeriv j hy hs)).self_of_nhds η]

/-- Two position derivatives of a local symbol commute. -/
theorem spatialDeriv_comm (j l : Fin n) (a : LocalSymbol U V W m) :
    spatialDeriv j (spatialDeriv l a) = spatialDeriv l (spatialDeriv j a) :=
  ext_of_mem fun y hy η => by
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    rw [← (eventually_coefficient_spatialDeriv j hy
        (eventually_coefficient_spatialDeriv l hy hs)).self_of_nhds η,
      ← (eventually_coefficient_spatialDeriv l hy
        (eventually_coefficient_spatialDeriv j hy hs)).self_of_nhds η,
      Symbol.spatialDeriv_comm]

theorem spatialDeriv_inclusion (j : Fin n) (h : m ≤ m') (a : LocalSymbol U V W m) :
    spatialDeriv j (inclusion h a) = inclusion h (spatialDeriv j a) :=
  ext_of_mem fun y hy η => by simp [hy]

/-- Restriction to a smaller open set commutes with position derivatives. -/
@[simp]
theorem restrict_spatialDeriv (h : U' ≤ U) (j : Fin n) (a : LocalSymbol U V W m) :
    restrict h (spatialDeriv j a) = spatialDeriv j (restrict h a) :=
  ext_of_mem fun y hy η => by
    rw [coefficient_restrict_of_mem h _ hy, coefficient_spatialDeriv_of_mem j _ (h hy),
      coefficient_spatialDeriv_of_mem j _ hy]
    refine (Filter.EventuallyEq.coordinateDeriv (f := fun z => a.coefficient (z, η))
      (g := fun z => (restrict h a).coefficient (z, η)) ?_ [j]).eq_of_nhds
    filter_upwards [U'.isOpen.mem_nhds hy] with z hz
    exact (coefficient_restrict_of_mem h a hz η).symm

end SpatialDeriv

section FrequencyDeriv

/-- If a symbol `s` on `ℝⁿ` agrees near `x` with a local symbol `a`, then the frequency
derivatives of their coefficients agree near `x`. -/
private theorem eventually_frequencyDerivCoeff (j : Fin n) {a : LocalSymbol U V W m}
    {s : Symbol n V W m} (hs : ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η)) :
    ∀ᶠ y in 𝓝 x, ∀ η, (Symbol.frequencyDeriv j s).coefficient (y, η) =
      coordinateDeriv [j] (fun ζ => a.coefficient (y, ζ)) η := by
  filter_upwards [hs] with y hy η
  rw [Symbol.coefficient_frequencyDeriv, funext hy]

/-- The frequency derivative of a local symbol, before bundling it as a linear map. -/
private def frequencyDerivAux (j : Fin n) (a : LocalSymbol U V W m) : LocalSymbol U V W (m - 1) :=
  ofEventuallyEq (fun p => coordinateDeriv [j] (fun η => a.coefficient (p.1, η)) p.2)
    (fun y hy η => by
      simp only [a.coefficient_of_notMem y hy]
      exact congrFun (coordinateDeriv_zero [j]) η)
    fun y hy => by
      obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
      exact ⟨Symbol.frequencyDeriv j s, eventually_frequencyDerivCoeff j hs⟩

private theorem coefficient_frequencyDerivAux (j : Fin n) (a : LocalSymbol U V W m)
    (x ξ : CoordinateSpace n) :
    (frequencyDerivAux j a).coefficient (x, ξ) =
      coordinateDeriv [j] (fun η => a.coefficient (x, η)) ξ := by
  rw [frequencyDerivAux, coefficient_ofEventuallyEq]

private theorem eventually_coefficient_frequencyDerivAux (j : Fin n) {a : LocalSymbol U V W m}
    {s : Symbol n V W m} (hs : ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η)) :
    ∀ᶠ y in 𝓝 x, ∀ η, (Symbol.frequencyDeriv j s).coefficient (y, η) =
      (frequencyDerivAux j a).coefficient (y, η) := by
  simpa only [coefficient_frequencyDerivAux] using eventually_frequencyDerivCoeff j hs

/-- The frequency derivative `∂_{ξ_j} a` of a symbol of order `m` on `U`, a symbol of order
`m - 1` on `U`. -/
def frequencyDeriv (j : Fin n) : LocalSymbol U V W m →ₗ[ℂ] LocalSymbol U V W (m - 1) where
  toFun := frequencyDerivAux j
  map_add' a b := ext_of_mem fun y hy η => by
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    obtain ⟨t, ht⟩ := b.exists_symbol_eventually_eq hy
    have hst : ∀ᶠ z in 𝓝 y, ∀ η, (s + t).coefficient (z, η) = (a + b).coefficient (z, η) := by
      filter_upwards [hs, ht] with z hzs hzt η
      simp [hzs η, hzt η]
    rw [← (eventually_coefficient_frequencyDerivAux j hst).self_of_nhds η, map_add,
      Symbol.coefficient_add, Pi.add_apply, coefficient_add, Pi.add_apply,
      (eventually_coefficient_frequencyDerivAux j hs).self_of_nhds η,
      (eventually_coefficient_frequencyDerivAux j ht).self_of_nhds η]
  map_smul' c a := ext_of_mem fun y hy η => by
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    have hcs : ∀ᶠ z in 𝓝 y, ∀ η, (c • s).coefficient (z, η) = (c • a).coefficient (z, η) := by
      filter_upwards [hs] with z hzs η
      simp [hzs η]
    rw [← (eventually_coefficient_frequencyDerivAux j hcs).self_of_nhds η, map_smul,
      Symbol.coefficient_smul, Pi.smul_apply, RingHom.id_apply, coefficient_smul, Pi.smul_apply,
      (eventually_coefficient_frequencyDerivAux j hs).self_of_nhds η]

@[simp]
theorem coefficient_frequencyDeriv (j : Fin n) (a : LocalSymbol U V W m)
    (x ξ : CoordinateSpace n) :
    (frequencyDeriv j a).coefficient (x, ξ) =
      coordinateDeriv [j] (fun η => a.coefficient (x, η)) ξ :=
  coefficient_frequencyDerivAux j a x ξ

/-- If a symbol `s` on `ℝⁿ` agrees near `x` with a local symbol `a`, then `∂_{ξ_j} s` agrees near
`x` with `∂_{ξ_j} a`. -/
theorem eventually_coefficient_frequencyDeriv (j : Fin n) {a : LocalSymbol U V W m}
    {s : Symbol n V W m} (hs : ∀ᶠ y in 𝓝 x, ∀ η, s.coefficient (y, η) = a.coefficient (y, η)) :
    ∀ᶠ y in 𝓝 x, ∀ η,
      (Symbol.frequencyDeriv j s).coefficient (y, η) = (frequencyDeriv j a).coefficient (y, η) :=
  eventually_coefficient_frequencyDerivAux j hs

/-- The mixed derivatives of `∂_{ξ_j} a` are those of `a` with one more frequency derivative. -/
@[simp]
theorem mixedDeriv_frequencyDeriv (j : Fin n) (a : LocalSymbol U V W m) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (frequencyDeriv j a).coefficient x ξ =
      mixedDeriv α (β ++ [j]) a.coefficient x ξ := by
  have h : (frequencyDeriv j a).coefficient =
      fun p => coordinateDeriv [j] (fun η => a.coefficient (p.1, η)) p.2 :=
    funext fun p => coefficient_frequencyDeriv j a p.1 p.2
  rw [h, mixedDeriv_coordinateDeriv_snd]

/-- The Leibniz rule for a frequency derivative of a composition. The orders `m' - 1 + m` and
`m' + (m - 1)` of the two terms are identified with the order `m' + m - 1` of the left side
through `TauCeti.LocalSymbol.inclusion`. -/
theorem frequencyDeriv_comp (j : Fin n) (b : LocalSymbol U W X m') (a : LocalSymbol U V W m) :
    frequencyDeriv j (b.comp a) =
      inclusion (by linarith) ((frequencyDeriv j b).comp a) +
        inclusion (by linarith) (b.comp (frequencyDeriv j a)) :=
  ext_of_mem fun y hy η => by
    obtain ⟨t, ht⟩ := b.exists_symbol_eventually_eq hy
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    have hts := eventually_coefficient_frequencyDeriv j (eventually_coefficient_comp ht hs)
    rw [← hts.self_of_nhds η, Symbol.frequencyDeriv_comp, Symbol.coefficient_add, Pi.add_apply,
      Symbol.coefficient_inclusion, Symbol.coefficient_inclusion, coefficient_add, Pi.add_apply,
      coefficient_inclusion, coefficient_inclusion,
      (eventually_coefficient_comp (eventually_coefficient_frequencyDeriv j ht) hs).self_of_nhds η,
      (eventually_coefficient_comp ht (eventually_coefficient_frequencyDeriv j hs)).self_of_nhds η]

/-- Two frequency derivatives of a local symbol commute. -/
theorem frequencyDeriv_comm (j l : Fin n) (a : LocalSymbol U V W m) :
    frequencyDeriv j (frequencyDeriv l a) = frequencyDeriv l (frequencyDeriv j a) :=
  ext_of_mem fun y hy η => by
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    rw [← (eventually_coefficient_frequencyDeriv j
        (eventually_coefficient_frequencyDeriv l hs)).self_of_nhds η,
      ← (eventually_coefficient_frequencyDeriv l
        (eventually_coefficient_frequencyDeriv j hs)).self_of_nhds η,
      Symbol.frequencyDeriv_comm]

/-- A position and a frequency derivative of a local symbol commute. -/
theorem spatialDeriv_frequencyDeriv_comm (j l : Fin n) (a : LocalSymbol U V W m) :
    spatialDeriv j (frequencyDeriv l a) = frequencyDeriv l (spatialDeriv j a) :=
  ext_of_mem fun y hy η => by
    obtain ⟨s, hs⟩ := a.exists_symbol_eventually_eq hy
    rw [← (eventually_coefficient_spatialDeriv j hy
        (eventually_coefficient_frequencyDeriv l hs)).self_of_nhds η,
      ← (eventually_coefficient_frequencyDeriv l
        (eventually_coefficient_spatialDeriv j hy hs)).self_of_nhds η,
      Symbol.spatialDeriv_frequencyDeriv_comm]

theorem frequencyDeriv_inclusion (j : Fin n) (h : m ≤ m') (a : LocalSymbol U V W m) :
    frequencyDeriv j (inclusion h a) = inclusion (by linarith) (frequencyDeriv j a) :=
  LocalSymbol.ext (funext fun ⟨y, η⟩ => by simp)

/-- Restriction to a smaller open set commutes with frequency derivatives. -/
@[simp]
theorem restrict_frequencyDeriv (h : U' ≤ U) (j : Fin n) (a : LocalSymbol U V W m) :
    restrict h (frequencyDeriv j a) = frequencyDeriv j (restrict h a) :=
  ext_of_mem fun y hy η => by
    simp only [coefficient_restrict_of_mem h _ hy, coefficient_frequencyDeriv]

end FrequencyDeriv

end LocalSymbol

namespace Symbol

variable {U : TopologicalSpace.Opens (CoordinateSpace n)} {V W X : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup X] [NormedSpace ℂ X] {m m' : ℝ}

/-- Over all of `ℝⁿ`, local composition is the composition of symbols on `ℝⁿ`. -/
theorem restrictTopEquiv_comp (b : Symbol n W X m') (a : Symbol n V W m) :
    restrictTopEquiv (b.comp a) = (restrictTopEquiv b).comp (restrictTopEquiv a) :=
  LocalSymbol.ext (funext fun p => by simp)

/-- Over all of `ℝⁿ`, the local position derivative is the position derivative of symbols on
`ℝⁿ`. -/
theorem restrictTopEquiv_spatialDeriv (j : Fin n) (a : Symbol n V W m) :
    restrictTopEquiv (spatialDeriv j a) = LocalSymbol.spatialDeriv j (restrictTopEquiv a) :=
  LocalSymbol.ext_of_mem fun y hy η => by simp [hy]

/-- Over all of `ℝⁿ`, the local frequency derivative is the frequency derivative of symbols on
`ℝⁿ`. -/
theorem restrictTopEquiv_frequencyDeriv (j : Fin n) (a : Symbol n V W m) :
    restrictTopEquiv (frequencyDeriv j a) = LocalSymbol.frequencyDeriv j (restrictTopEquiv a) :=
  LocalSymbol.ext (funext fun ⟨y, η⟩ => by simp)

/-- Restricting a composition of symbols on `ℝⁿ` to `U` composes the restrictions. -/
@[simp]
theorem restrict_comp (b : Symbol n W X m') (a : Symbol n V W m) :
    (b.comp a).restrict U = (b.restrict U).comp (a.restrict U) := by
  rw [← restrict_restrictTopEquiv le_top, restrictTopEquiv_comp, LocalSymbol.restrict_comp,
    restrict_restrictTopEquiv, restrict_restrictTopEquiv]

/-- Restricting the position derivative of a symbol on `ℝⁿ` to `U` gives the position derivative
of the restriction. -/
@[simp]
theorem restrict_spatialDeriv (j : Fin n) (a : Symbol n V W m) :
    (spatialDeriv j a).restrict U = LocalSymbol.spatialDeriv j (a.restrict U) := by
  rw [← restrict_restrictTopEquiv le_top, restrictTopEquiv_spatialDeriv,
    LocalSymbol.restrict_spatialDeriv, restrict_restrictTopEquiv]

/-- Restricting the frequency derivative of a symbol on `ℝⁿ` to `U` gives the frequency derivative
of the restriction. -/
@[simp]
theorem restrict_frequencyDeriv (j : Fin n) (a : Symbol n V W m) :
    (frequencyDeriv j a).restrict U = LocalSymbol.frequencyDeriv j (a.restrict U) := by
  rw [← restrict_restrictTopEquiv le_top, restrictTopEquiv_frequencyDeriv,
    LocalSymbol.restrict_frequencyDeriv, restrict_restrictTopEquiv]

end Symbol

end TauCeti
