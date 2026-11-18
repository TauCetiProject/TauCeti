/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Hyperfunction.OneDimensional
public import Mathlib.Topology.Sets.Compacts
public import TauCeti.Analysis.Contour.Cycle.Basic
import TauCeti.Topology.Sets.Closeds
import TauCeti.Topology.Sets.Compacts
import TauCeti.Analysis.Complex.SeparationOfSingularities

/-!
# Holomorphic functions vanishing at infinity and hyperfunctions with compact support

Let `K` be a compact subset of `ℂ`. A holomorphic function on `V ∖ K`, for an open `V ⊇ K`,
determines a class in `O(V ∖ K) / O(V)`, its singular part along `K`. By the separation of
singularities (`IsCompact.exists_eqOn_add_tendsto_cocompact`), every such class has exactly one
representative that is holomorphic on all of `ℂ ∖ K` and tends to `0` at infinity. This file
records this in the ambient-function encoding of
`TauCeti/Analysis/Hyperfunction/OneDimensional.lean`, as two complex-linear isomorphisms.

* For compact `K ⊆ V ⊆ ℂ`, the space `O₀(ℂ ∖ K)` of holomorphic functions on `ℂ ∖ K` vanishing at
  infinity is isomorphic to `O(V ∖ K) / O(V)`, by restricting to `V ∖ K`
  (`TauCeti.Hyperfunction.vanishingAtInfinityEquiv`). The isomorphisms for different `V` are
  compatible with restriction, so the quotient does not depend on `V`.
* For a compact set `K` of the real line and an open set `U ⊆ ℝ` containing it, the
  one-dimensional hyperfunctions on `U` supported in `K`, the classes in `O(ℂ ∖ ℝ) / O(W(U))`
  whose restriction to `U ∖ K` vanishes, are isomorphic to `O₀(ℂ ∖ K)`
  (`TauCeti.Hyperfunction.vanishingAtInfinityEquivSupported`). A hyperfunction supported in `K`
  thus has a canonical representative holomorphic on `ℂ ∖ K` and vanishing at infinity, and the
  space of such hyperfunctions does not depend on `U`.

The representative in `O₀(ℂ ∖ K)` of the class of `f ∈ O(V ∖ K)` is the Cauchy integral
`w ↦ -(2πi)⁻¹ ∮_Γ f(z)/(z - w) dz` over a cycle `Γ` around `K` in `V ∖ K`
(`TauCeti.Hyperfunction.vanishingAtInfinityEquiv_symm_mk_apply`).

## Main declarations

* `TauCeti.Hyperfunction.vanishingAtInfinitySections K`: the holomorphic functions on `ℂ ∖ K`
  tending to `0` at infinity.
* `TauCeti.Hyperfunction.throughCompact K V`: the holomorphic functions on `V ∖ K` extending
  holomorphically across `K`.
* `TauCeti.Hyperfunction.vanishingAtInfinityEquiv`: the isomorphism
  `O₀(ℂ ∖ K) ≃ O(V ∖ K) / O(V)`, with its naturality in `V`
  (`TauCeti.Hyperfunction.mapQ_vanishingAtInfinityEquiv`) and the Cauchy integral formula for its
  inverse (`TauCeti.Hyperfunction.vanishingAtInfinityEquiv_symm_mk_apply`).
* `TauCeti.Hyperfunction.vanishingAtInfinityToHyperfunction`: the class in `O(ℂ ∖ ℝ) / O(W(U))` of
  a function in `O₀(ℂ ∖ K)` for compact `K ⊆ ℝ`, with
  `TauCeti.Hyperfunction.vanishingAtInfinityToHyperfunction_injective` and
  `TauCeti.Hyperfunction.range_vanishingAtInfinityToHyperfunction` (its range is the kernel of the
  restriction to `U ∖ K`), packaged as `TauCeti.Hyperfunction.vanishingAtInfinityEquivSupported`.

## References

* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40, §1.
* A. Kaneko, *Introduction to hyperfunctions*, Chapter 1.
* L. Hörmander, *The analysis of linear partial differential operators I*, §9.1.
-/

public section

noncomputable section

open Filter Set TopologicalSpace

open scoped Real Topology

namespace TauCeti.Hyperfunction

/-! ### Holomorphic functions vanishing at infinity -/

/-- The holomorphic functions on `ℂ ∖ K` that tend to `0` at infinity, for a compact set
`K ⊆ ℂ`, in the ambient-function encoding of `holomorphicSections`. -/
def vanishingAtInfinitySections (K : Compacts ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {h | h ∈ holomorphicSections K.toCloseds.compl ∧ Tendsto h (cocompact ℂ) (𝓝 0)}
  zero_mem' := ⟨zero_mem _, tendsto_const_nhds⟩
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, by rw [← add_zero (0 : ℂ)]; exact hf.2.add hg.2⟩
  smul_mem' c _ hf := ⟨Submodule.smul_mem _ c hf.1, by rw [← smul_zero c]; exact hf.2.const_smul c⟩

theorem mem_vanishingAtInfinitySections_iff {K : Compacts ℂ} {h : ℂ → ℂ} :
    h ∈ vanishingAtInfinitySections K ↔
      h ∈ holomorphicSections K.toCloseds.compl ∧ Tendsto h (cocompact ℂ) (𝓝 0) :=
  Iff.rfl

theorem vanishingAtInfinitySections_le_holomorphicSections (K : Compacts ℂ) :
    vanishingAtInfinitySections K ≤ holomorphicSections K.toCloseds.compl :=
  fun _ hh => (mem_vanishingAtInfinitySections_iff.mp hh).1

/-- The three properties of a function in `O₀(ℂ ∖ K)`: holomorphic off `K`, zero on `K`, and
vanishing at infinity. -/
private theorem of_mem_vanishingAtInfinitySections {K : Compacts ℂ} {h : ℂ → ℂ}
    (hh : h ∈ vanishingAtInfinitySections K) :
    DifferentiableOn ℂ h (K : Set ℂ)ᶜ ∧ (∀ z ∈ (K : Set ℂ), h z = 0) ∧
      Tendsto h (cocompact ℂ) (𝓝 0) := by
  obtain ⟨hhol, hlim⟩ := mem_vanishingAtInfinitySections_iff.mp hh
  obtain ⟨hd, hz⟩ := mem_holomorphicSections_iff.mp hhol
  exact ⟨hd, fun z hzK => hz z (not_not_intro hzK), hlim⟩

/-- The singular part `h` of a separation of singularities, made zero on `K`, lies in
`O₀(ℂ ∖ K)`. -/
private theorem indicator_mem_vanishingAtInfinitySections {K : Compacts ℂ} {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (K : Set ℂ)ᶜ) (hlim : Tendsto h (cocompact ℂ) (𝓝 0)) :
    (K : Set ℂ)ᶜ.indicator h ∈ vanishingAtInfinitySections K :=
  ⟨indicator_mem_holomorphicSections_of_differentiableOn (U := K.toCloseds.compl) hh,
    hlim.congr' (eventuallyEq_of_mem K.isCompact.compl_mem_cocompact fun _ hz =>
      (indicator_of_mem hz h).symm)⟩

/-- At a point of `V ∖ K` where `f = g + h`, minus the regular part `g` made zero off `V` is the
singular part `h` made zero on `K`, minus `f`. -/
private theorem neg_indicator_eq_indicator_sub {V K : Set ℂ} {f g h : ℂ → ℂ} {z : ℂ}
    (hzV : z ∈ V) (hzK : z ∉ K) (hfz : f z = (g + h) z) :
    (-V.indicator g) z = Kᶜ.indicator h z - f z := by
  rw [Pi.neg_apply, indicator_of_mem hzV, indicator_of_mem (mem_compl hzK), hfz, Pi.add_apply]
  ring

/-! ### The quotient `O(V ∖ K) / O(V)` -/

/-- The holomorphic functions on `V ∖ K` that extend holomorphically across the compact set `K`,
that is, that are restrictions of holomorphic functions on `V`. -/
def throughCompact (K : Compacts ℂ) (V : Opens ℂ) :
    Submodule ℂ (holomorphicSections (V ⊓ K.toCloseds.compl)) :=
  LinearMap.range (holomorphicRestrict inf_le_left)

/-- A holomorphic function on `V ∖ K` extends across `K` exactly when it agrees on `V ∖ K` with a
holomorphic function on `V`. -/
theorem mem_throughCompact_iff {K : Compacts ℂ} {V : Opens ℂ}
    {f : holomorphicSections (V ⊓ K.toCloseds.compl)} :
    f ∈ throughCompact K V ↔ ∃ g ∈ holomorphicSections V, EqOn g f ((V : Set ℂ) \ K) := by
  refine ⟨fun ⟨g, hg⟩ => ⟨g, g.2, fun z hz => ?_⟩, fun ⟨g, hg, hgf⟩ => ⟨⟨g, hg⟩, ?_⟩⟩
  · rw [← hg, coe_holomorphicRestrict,
      indicator_of_mem (Compacts.mem_inf_compl_toCloseds.mpr hz)]
  · refine Subtype.ext (funext fun z => ?_)
    by_cases hz : z ∈ V ⊓ K.toCloseds.compl
    · rw [coe_holomorphicRestrict, indicator_of_mem hz]
      exact hgf (Compacts.mem_inf_compl_toCloseds.mp hz)
    · rw [coe_holomorphicRestrict, indicator_of_notMem hz]
      exact ((mem_holomorphicSections_iff.mp f.2).2 z hz).symm

/-- The map `O₀(ℂ ∖ K) → O(V ∖ K) / O(V)` sending a function to the class of its restriction. -/
def vanishingAtInfinityToQuotient (K : Compacts ℂ) (V : Opens ℂ) :
    vanishingAtInfinitySections K →ₗ[ℂ]
      holomorphicSections (V ⊓ K.toCloseds.compl) ⧸ throughCompact K V :=
  (throughCompact K V).mkQ ∘ₗ holomorphicRestrict inf_le_right ∘ₗ
    Submodule.inclusion (vanishingAtInfinitySections_le_holomorphicSections K)

@[simp]
theorem vanishingAtInfinityToQuotient_apply (K : Compacts ℂ) (V : Opens ℂ)
    (h : vanishingAtInfinitySections K) :
    vanishingAtInfinityToQuotient K V h = Submodule.Quotient.mk (holomorphicRestrict inf_le_right
      ⟨h, vanishingAtInfinitySections_le_holomorphicSections K h.2⟩) :=
  (rfl)

/-- A function in `O₀(ℂ ∖ K)` whose restriction to `V ∖ K` extends across `K` is zero. -/
theorem vanishingAtInfinityToQuotient_injective {K : Compacts ℂ} {V : Opens ℂ}
    (hKV : (K : Set ℂ) ⊆ V) : Function.Injective (vanishingAtInfinityToQuotient K V) := by
  refine (injective_iff_map_eq_zero _).mpr fun h hh => ?_
  rw [vanishingAtInfinityToQuotient_apply, Submodule.Quotient.mk_eq_zero,
    mem_throughCompact_iff] at hh
  obtain ⟨g, hg, hgh⟩ := hh
  obtain ⟨hd, hK, hlim⟩ := of_mem_vanishingAtInfinitySections h.2
  have hzero := K.isCompact.eqOn_zero_of_eqOn_of_tendsto_cocompact V.isOpen hKV
    (mem_holomorphicSections_iff.mp hg).1 hd hlim fun z hz => (hgh hz).trans
      (by rw [coe_holomorphicRestrict,
        indicator_of_mem (Compacts.mem_inf_compl_toCloseds.mpr hz)])
  refine Subtype.ext (funext fun z => ?_)
  by_cases hzK : z ∈ (K : Set ℂ)
  exacts [hK z hzK, hzero.2 hzK]

/-- Every class in `O(V ∖ K) / O(V)` is represented by a function in `O₀(ℂ ∖ K)`, by the
separation of singularities along `K`. -/
theorem vanishingAtInfinityToQuotient_surjective {K : Compacts ℂ} {V : Opens ℂ}
    (hKV : (K : Set ℂ) ⊆ V) : Function.Surjective (vanishingAtInfinityToQuotient K V) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H f =>
    obtain ⟨hfd, -⟩ := mem_holomorphicSections_iff.mp f.2
    obtain ⟨g, h, hg, hh, hlim, hfgh⟩ :=
      K.isCompact.exists_eqOn_add_tendsto_cocompact V.isOpen hKV hfd
    refine ⟨⟨_, indicator_mem_vanishingAtInfinitySections hh hlim⟩, ?_⟩
    rw [vanishingAtInfinityToQuotient_apply, Submodule.Quotient.eq, mem_throughCompact_iff]
    -- The difference with `f` is minus the regular part.
    refine ⟨-(V : Set ℂ).indicator g, neg_mem
      (indicator_mem_holomorphicSections_of_differentiableOn hg), fun z hz => ?_⟩
    rw [Submodule.coe_sub, Pi.sub_apply, coe_holomorphicRestrict,
      indicator_of_mem (Compacts.mem_inf_compl_toCloseds.mpr hz)]
    exact neg_indicator_eq_indicator_sub hz.1 hz.2 (hfgh hz)

/-- **The quotient `O(V ∖ K) / O(V)` is the space of holomorphic functions on `ℂ ∖ K` vanishing at
infinity.** For a compact set `K` contained in an open set `V ⊆ ℂ`, restriction to `V ∖ K` induces
a complex-linear isomorphism `O₀(ℂ ∖ K) ≃ O(V ∖ K) / O(V)`. -/
def vanishingAtInfinityEquiv {K : Compacts ℂ} {V : Opens ℂ} (hKV : (K : Set ℂ) ⊆ V) :
    vanishingAtInfinitySections K ≃ₗ[ℂ]
      holomorphicSections (V ⊓ K.toCloseds.compl) ⧸ throughCompact K V :=
  LinearEquiv.ofBijective (vanishingAtInfinityToQuotient K V)
    ⟨vanishingAtInfinityToQuotient_injective hKV, vanishingAtInfinityToQuotient_surjective hKV⟩

@[simp]
theorem vanishingAtInfinityEquiv_apply {K : Compacts ℂ} {V : Opens ℂ} (hKV : (K : Set ℂ) ⊆ V)
    (h : vanishingAtInfinitySections K) :
    vanishingAtInfinityEquiv hKV h = vanishingAtInfinityToQuotient K V h :=
  (rfl)

/-- **The inverse of `vanishingAtInfinityEquiv` is a Cauchy integral.** The function in
`O₀(ℂ ∖ K)` representing the class of `f ∈ O(V ∖ K)` is `w ↦ -(2πi)⁻¹ ∮_Γ f(z)/(z - w) dz`, for a
cycle `Γ` in `V ∖ K`, null-homologous in `V` and winding once around every point of `K`, at every
point `w` off `Γ` around which `Γ` winds zero times. -/
theorem vanishingAtInfinityEquiv_symm_mk_apply {K : Compacts ℂ} {V : Opens ℂ}
    (hKV : (K : Set ℂ) ⊆ V) (f : holomorphicSections (V ⊓ K.toCloseds.compl))
    {Γ : Contour.Cycle} (hΓ : Γ.IsIn ((V : Set ℂ) \ K)) (hΓV : Γ.IsNullHomologous V)
    (hΓK : ∀ z ∈ (K : Set ℂ), Contour.Cycle.windingNumber z Γ = 1) {w : ℂ}
    (hw : w ∉ Contour.Cycle.trace Γ) (hw₀ : Contour.Cycle.windingNumber w Γ = 0) :
    ((vanishingAtInfinityEquiv hKV).symm (Submodule.Quotient.mk f) : ℂ → ℂ) w =
      -(2 * π * Complex.I)⁻¹ * Contour.Cycle.integral (fun z ↦ (f : ℂ → ℂ) z / (z - w)) Γ := by
  set h := (vanishingAtInfinityEquiv hKV).symm (Submodule.Quotient.mk f)
  have hq : vanishingAtInfinityToQuotient K V h = Submodule.Quotient.mk f :=
    (vanishingAtInfinityEquiv hKV).apply_symm_apply _
  rw [vanishingAtInfinityToQuotient_apply, Submodule.Quotient.eq, mem_throughCompact_iff] at hq
  obtain ⟨g, hg, hgf⟩ := hq
  obtain ⟨hd, -, hlim⟩ := of_mem_vanishingAtInfinitySections h.2
  -- `f = -g + h` on `V ∖ K`, so `h` is the singular part of `f`.
  have hfgh : EqOn f ((fun z => -g z) + (h : ℂ → ℂ)) ((V : Set ℂ) \ K) := fun z hz => by
    have hz' := hgf hz
    rw [Submodule.coe_sub, Pi.sub_apply, coe_holomorphicRestrict,
      indicator_of_mem (Compacts.mem_inf_compl_toCloseds.mpr hz)] at hz'
    simp only [Pi.add_apply]
    linear_combination hz'
  have hint := K.isCompact.integral_div_sub_eq_of_windingNumber_eq_zero V.isOpen hKV
    (mem_holomorphicSections_iff.mp hg).1.neg hd hlim hfgh hΓ hΓV hΓK hw hw₀
  rw [hint]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Restriction maps functions on `V ∖ K` extending across `K` to functions on `V' ∖ K` extending
across `K`. -/
theorem throughCompact_le_comap {K : Compacts ℂ} {V' V : Opens ℂ} (h : V' ≤ V) :
    throughCompact K V ≤
      (throughCompact K V').comap (holomorphicRestrict (inf_le_inf_right _ h)) := by
  rintro _ ⟨g, rfl⟩
  exact ⟨holomorphicRestrict h g, by simp only [holomorphicRestrict_holomorphicRestrict]⟩

/-- **Naturality in `V`.** For compact `K ⊆ V' ⊆ V`, restricting classes from `V ∖ K` to `V' ∖ K`
intertwines the isomorphisms `O₀(ℂ ∖ K) ≃ O(V ∖ K) / O(V)` and `O₀(ℂ ∖ K) ≃ O(V' ∖ K) / O(V')`.
In particular the restriction `O(V ∖ K) / O(V) → O(V' ∖ K) / O(V')` is an isomorphism. -/
theorem mapQ_vanishingAtInfinityEquiv {K : Compacts ℂ} {V' V : Opens ℂ}
    (hKV' : (K : Set ℂ) ⊆ V') (h : V' ≤ V) (q : vanishingAtInfinitySections K) :
    (throughCompact K V).mapQ (throughCompact K V')
        (holomorphicRestrict (inf_le_inf_right _ h)) (throughCompact_le_comap h)
        (vanishingAtInfinityEquiv (hKV'.trans h) q) =
      vanishingAtInfinityEquiv hKV' q := by
  simp only [vanishingAtInfinityEquiv_apply, vanishingAtInfinityToQuotient_apply,
    Submodule.mapQ_apply, holomorphicRestrict_holomorphicRestrict]

/-! ### Hyperfunctions supported in a compact subset of the real line -/

/-- A compact set of the real line, as a compact set of `ℂ`. -/
def ofRealCompacts (K : Compacts ℝ) : Compacts ℂ :=
  K.map ((↑) : ℝ → ℂ) Complex.continuous_ofReal

@[simp, norm_cast]
theorem coe_ofRealCompacts (K : Compacts ℝ) :
    (ofRealCompacts K : Set ℂ) = ((↑) : ℝ → ℂ) '' K :=
  Compacts.coe_map _ K

theorem mem_ofRealCompacts_iff {K : Compacts ℝ} {z : ℂ} :
    z ∈ ofRealCompacts K ↔ z.im = 0 ∧ z.re ∈ K := by
  rw [← SetLike.mem_coe, coe_ofRealCompacts]
  refine ⟨?_, fun ⟨him, hre⟩ => ⟨z.re, hre, Complex.ext rfl him.symm⟩⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨Complex.ofReal_im x, hx⟩

/-- The non-real complex numbers avoid a compact set of the real line. -/
theorem nonRealOpen_le_compl_ofRealCompacts (K : Compacts ℝ) :
    nonRealOpen ≤ (ofRealCompacts K).toCloseds.compl := fun _ hz hzK =>
  mem_nonRealOpen_iff.mp hz (mem_ofRealCompacts_iff.mp hzK).1

/-- A compact set of an open set `U ⊆ ℝ` lies in `W(U)`. -/
theorem ofRealCompacts_subset_complexNeighborhood {K : Compacts ℝ} {U : Opens ℝ}
    (hKU : (K : Set ℝ) ⊆ U) : (ofRealCompacts K : Set ℂ) ⊆ complexNeighborhood U :=
  fun _ hz => mem_complexNeighborhood_iff.mpr (Or.inr (hKU (mem_ofRealCompacts_iff.mp hz).2))

/-- The open set `W(U ∖ K)` is `W(U) ∖ K`. -/
theorem complexNeighborhood_inf_compl (U : Opens ℝ) (K : Compacts ℝ) :
    complexNeighborhood (U ⊓ K.toCloseds.compl) =
      complexNeighborhood U ⊓ (ofRealCompacts K).toCloseds.compl := by
  ext z
  simp only [SetLike.mem_coe, Opens.mem_inf, mem_complexNeighborhood_iff,
    Closeds.mem_compl, Compacts.mem_toCloseds, mem_ofRealCompacts_iff]
  by_cases him : z.im = 0 <;> simp [him]

/-- The class in `O(ℂ ∖ ℝ) / O(W(U))` of a holomorphic function on `ℂ ∖ K` vanishing at infinity,
for a compact set `K` of the real line: the hyperfunction on `U` represented by its restriction to
`ℂ ∖ ℝ`. -/
def vanishingAtInfinityToHyperfunction (K : Compacts ℝ) (U : Opens ℝ) :
    vanishingAtInfinitySections (ofRealCompacts K) →ₗ[ℂ] OneDimBoundaryQuotient U :=
  (throughReal U).mkQ ∘ₗ holomorphicRestrict (nonRealOpen_le_compl_ofRealCompacts K) ∘ₗ
    Submodule.inclusion (vanishingAtInfinitySections_le_holomorphicSections _)

@[simp]
theorem vanishingAtInfinityToHyperfunction_apply (K : Compacts ℝ) (U : Opens ℝ)
    (h : vanishingAtInfinitySections (ofRealCompacts K)) :
    vanishingAtInfinityToHyperfunction K U h =
      Submodule.Quotient.mk (holomorphicRestrict (nonRealOpen_le_compl_ofRealCompacts K)
        ⟨h, vanishingAtInfinitySections_le_holomorphicSections _ h.2⟩) :=
  (rfl)

/-- The hyperfunction class of a function in `O₀(ℂ ∖ K)` is compatible with restriction. -/
theorem oneDimBoundaryRestrict_vanishingAtInfinityToHyperfunction (K : Compacts ℝ)
    {U' U : Opens ℝ} (h : U' ≤ U) (q : vanishingAtInfinitySections (ofRealCompacts K)) :
    oneDimBoundaryRestrict h (vanishingAtInfinityToHyperfunction K U q) =
      vanishingAtInfinityToHyperfunction K U' q := by
  rw [vanishingAtInfinityToHyperfunction_apply, vanishingAtInfinityToHyperfunction_apply,
    oneDimBoundaryRestrict_mk]

/-- **Injectivity.** For a compact set `K` contained in an open set `U ⊆ ℝ`, a holomorphic
function on `ℂ ∖ K` vanishing at infinity whose hyperfunction class on `U` is zero is zero. -/
theorem vanishingAtInfinityToHyperfunction_injective {K : Compacts ℝ} {U : Opens ℝ}
    (hKU : (K : Set ℝ) ⊆ U) : Function.Injective (vanishingAtInfinityToHyperfunction K U) := by
  refine (injective_iff_map_eq_zero _).mpr fun h hh => ?_
  rw [vanishingAtInfinityToHyperfunction_apply, Submodule.Quotient.mk_eq_zero,
    mem_throughReal_iff] at hh
  obtain ⟨g, hg, hgh⟩ := hh
  obtain ⟨hd, hK, hlim⟩ := of_mem_vanishingAtInfinitySections h.2
  -- The extension `g` agrees with `h` on `W(U) ∖ K`, the real points being limits of non-real ones.
  have hgh' : EqOn g h (complexNeighborhood U ⊓ (ofRealCompacts K).toCloseds.compl :) :=
    eqOn_inf_of_eqOn_nonRealOpen (mem_holomorphicSections_iff.mp hg).1.continuousOn
      hd.continuousOn (nonRealOpen_le_complexNeighborhood U) (nonRealOpen_le_compl_ofRealCompacts K)
      fun z hz => (hgh hz).trans (by rw [coe_holomorphicRestrict, indicator_of_mem hz])
  have hzero := (ofRealCompacts K).isCompact.eqOn_zero_of_eqOn_of_tendsto_cocompact
    (complexNeighborhood U).isOpen (ofRealCompacts_subset_complexNeighborhood hKU)
    (mem_holomorphicSections_iff.mp hg).1 hd hlim fun z hz => hgh' hz
  refine Subtype.ext (funext fun z => ?_)
  by_cases hzK : z ∈ (ofRealCompacts K : Set ℂ)
  exacts [hK z hzK, hzero.2 hzK]

/-- **The hyperfunctions supported in `K`.** For a compact set `K` contained in an open set
`U ⊆ ℝ`, the hyperfunctions on `U` whose restriction to `U ∖ K` vanishes are exactly the classes of
holomorphic functions on `ℂ ∖ K` vanishing at infinity. -/
theorem range_vanishingAtInfinityToHyperfunction {K : Compacts ℝ} {U : Opens ℝ}
    (hKU : (K : Set ℝ) ⊆ U) :
    LinearMap.range (vanishingAtInfinityToHyperfunction K U) =
      LinearMap.ker (oneDimBoundaryRestrict (inf_le_left : U ⊓ K.toCloseds.compl ≤ U)) := by
  refine le_antisymm ?_ fun q hq => ?_
  · -- A function holomorphic off `K` extends across `U ∖ K`, where `W(U ∖ K) = W(U) ∖ K`.
    rintro _ ⟨h, rfl⟩
    obtain ⟨hd, -, -⟩ := of_mem_vanishingAtInfinitySections h.2
    rw [LinearMap.mem_ker, oneDimBoundaryRestrict_vanishingAtInfinityToHyperfunction,
      vanishingAtInfinityToHyperfunction_apply, Submodule.Quotient.mk_eq_zero,
      mem_throughReal_iff]
    refine ⟨_, indicator_mem_holomorphicSections_of_differentiableOn
      (hd.mono (complexNeighborhood_inf_compl U K ▸ inf_le_right)), fun z hz => ?_⟩
    rw [indicator_of_mem (nonRealOpen_le_complexNeighborhood _ hz), coe_holomorphicRestrict,
      indicator_of_mem hz]
  · -- A representative extending across `U ∖ K` has its singular part along `K` in `O₀(ℂ ∖ K)`.
    induction q using Submodule.Quotient.induction_on with
    | H f =>
      rw [LinearMap.mem_ker, oneDimBoundaryRestrict_mk, Submodule.Quotient.mk_eq_zero,
        mem_throughReal_iff, complexNeighborhood_inf_compl] at hq
      obtain ⟨F, hF, hFf⟩ := hq
      obtain ⟨g, h, hg, hh, hlim, hFgh⟩ :=
        (ofRealCompacts K).isCompact.exists_eqOn_add_tendsto_cocompact
          (complexNeighborhood U).isOpen (ofRealCompacts_subset_complexNeighborhood hKU)
          (mem_holomorphicSections_iff.mp hF).1
      refine ⟨⟨_, indicator_mem_vanishingAtInfinitySections hh hlim⟩, ?_⟩
      rw [vanishingAtInfinityToHyperfunction_apply, Submodule.Quotient.eq, mem_throughReal_iff]
      -- The difference with `f` is minus the regular part, holomorphic on `W(U)`.
      refine ⟨-(complexNeighborhood U : Set ℂ).indicator g, neg_mem
        (indicator_mem_holomorphicSections_of_differentiableOn hg), fun z hz => ?_⟩
      have hzW : z ∈ complexNeighborhood U := nonRealOpen_le_complexNeighborhood U hz
      have hzK : z ∈ (ofRealCompacts K).toCloseds.compl :=
        nonRealOpen_le_compl_ofRealCompacts K hz
      rw [Submodule.coe_sub, Pi.sub_apply, coe_holomorphicRestrict, indicator_of_mem hz, ← hFf hz]
      exact neg_indicator_eq_indicator_sub hzW (Closeds.mem_compl.mp hzK) (hFgh ⟨hzW, hzK⟩)

/-- **Hyperfunctions with compact support.** For a compact set `K` contained in an open set
`U ⊆ ℝ`, the space of one-dimensional hyperfunctions on `U` supported in `K`, the classes in
`O(ℂ ∖ ℝ) / O(W(U))` whose restriction to `U ∖ K` vanishes, is isomorphic to the space of
holomorphic functions on `ℂ ∖ K` vanishing at infinity. -/
def vanishingAtInfinityEquivSupported {K : Compacts ℝ} {U : Opens ℝ} (hKU : (K : Set ℝ) ⊆ U) :
    vanishingAtInfinitySections (ofRealCompacts K) ≃ₗ[ℂ]
      LinearMap.ker (oneDimBoundaryRestrict (inf_le_left : U ⊓ K.toCloseds.compl ≤ U)) :=
  (LinearEquiv.ofInjective _ (vanishingAtInfinityToHyperfunction_injective hKU)).trans
    (LinearEquiv.ofEq _ _ (range_vanishingAtInfinityToHyperfunction hKU))

@[simp]
theorem coe_vanishingAtInfinityEquivSupported_apply {K : Compacts ℝ} {U : Opens ℝ}
    (hKU : (K : Set ℝ) ⊆ U) (h : vanishingAtInfinitySections (ofRealCompacts K)) :
    (vanishingAtInfinityEquivSupported hKU h : OneDimBoundaryQuotient U) =
      vanishingAtInfinityToHyperfunction K U h :=
  (rfl)

end TauCeti.Hyperfunction
