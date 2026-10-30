/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Analysis.Complex.ReImTopology

/-!
# One-dimensional hyperfunctions as boundary values of holomorphic functions

In one variable, Sato's hyperfunctions on an open set `U ⊆ ℝ` can be written as differences of
boundary values of holomorphic functions. Put `W(U) = ℂ ∖ (ℝ ∖ U)`, the largest open subset of
`ℂ` whose intersection with `ℝ` is `U`. A hyperfunction on `U` is represented by
a holomorphic function `f` on `ℂ ∖ ℝ`, that is, by a pair of holomorphic functions on the upper
and the lower half-plane, and two representatives give the same hyperfunction when their
difference extends holomorphically across `U`, i.e. to all of `W(U)`. The space of hyperfunctions
on `U` is the quotient `O(ℂ ∖ ℝ) / O(W(U))`. Restriction to a smaller open `V ⊆ U` keeps the
representative: a function extending across `U` also extends across `V`.

## Encoding

Holomorphic functions on an open `U ⊆ ℂ` are encoded as genuine functions `ℂ → ℂ` that are
complex differentiable on `U` and vanish outside `U`
(`TauCeti.Hyperfunction.holomorphicSections`). The extension by zero is only a device for using
one ambient module of functions; no continuity across the boundary of `U` is imposed or used.
Restriction to a smaller open multiplies by the indicator function
(`TauCeti.Hyperfunction.holomorphicRestrict`).

## Main declarations

* `TauCeti.Hyperfunction.nonRealOpen`: the open set `ℂ ∖ ℝ`, which is dense
  (`TauCeti.Hyperfunction.dense_nonRealOpen`);
* `TauCeti.Hyperfunction.complexNeighborhood U`: the open set `W(U) = ℂ ∖ (ℝ ∖ U)`;
* `TauCeti.Hyperfunction.throughReal U`: the holomorphic functions on `ℂ ∖ ℝ` that extend
  holomorphically to `W(U)`;
* `TauCeti.Hyperfunction.OneDimBoundaryQuotient U`: the quotient `O(ℂ ∖ ℝ) / O(W(U))`, and
  `TauCeti.Hyperfunction.oneDimBoundaryPresheaf` the presheaf of complex vector spaces
  `U ↦ O(ℂ ∖ ℝ) / O(W(U))` on `ℝ`. All its restriction maps are surjective
  (`TauCeti.Hyperfunction.oneDimBoundaryRestrict_surjective`).

## Main results

* `TauCeti.Hyperfunction.throughReal_iSup`: a holomorphic function on `ℂ ∖ ℝ` extends across
  `⋃ i, U i` exactly when it extends across every `U i`. The local extensions agree on the real
  points of the overlaps, because they are continuous there and agree on the dense set `ℂ ∖ ℝ`, so
  they glue.
* `TauCeti.Hyperfunction.oneDimBoundaryPresheaf_isSeparated`: consequently the presheaf
  `U ↦ O(ℂ ∖ ℝ) / O(W(U))` is separated: a section that vanishes locally vanishes. This is the
  uniqueness half of the sheaf property. The existence half needs the vanishing of the first
  cohomology of the sheaf of holomorphic functions on open subsets of `ℂ` (a Cousin problem) and is
  not proved here.

## References

* M. Sato, *Theory of hyperfunctions I*, J. Fac. Sci. Univ. Tokyo Sect. I 8 (1959), 139–193.
* H. Komatsu, *An introduction to the theory of hyperfunctions*, in *Hyperfunctions and
  pseudo-differential equations*, Lecture Notes in Mathematics 287 (1973), 3–40.
* L. Hörmander, *The analysis of linear partial differential operators I*, §9.1.
-/

public section

noncomputable section

open CategoryTheory Opposite Set TopologicalSpace

namespace TauCeti.Hyperfunction

/-! ### Holomorphic sections -/

/-- The holomorphic functions on an open set `U ⊆ ℂ`, encoded as the functions `ℂ → ℂ` that are
complex differentiable on `U` and vanish outside `U`. -/
def holomorphicSections (U : Opens ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | DifferentiableOn ℂ f U ∧ ∀ z, z ∉ U → f z = 0}
  zero_mem' := ⟨differentiableOn_const 0, fun _ _ => rfl⟩
  add_mem' hf hg :=
    ⟨hf.1.add hg.1, fun z hz => by simp [hf.2 z hz, hg.2 z hz]⟩
  smul_mem' c _ hf :=
    ⟨hf.1.const_smul c, fun z hz => by simp [hf.2 z hz]⟩

theorem mem_holomorphicSections_iff {U : Opens ℂ} {f : ℂ → ℂ} :
    f ∈ holomorphicSections U ↔ DifferentiableOn ℂ f U ∧ ∀ z, z ∉ U → f z = 0 :=
  Iff.rfl

/-- The indicator function of a smaller open set restricts holomorphic sections. -/
theorem indicator_mem_holomorphicSections {U V : Opens ℂ} (h : U ≤ V) {f : ℂ → ℂ}
    (hf : f ∈ holomorphicSections V) : (U : Set ℂ).indicator f ∈ holomorphicSections U :=
  ⟨(hf.1.mono h).congr fun _ hz => indicator_of_mem hz f,
    fun _ hz => indicator_of_notMem hz f⟩

/-- Restriction of holomorphic sections to a smaller open set. -/
def holomorphicRestrict {U V : Opens ℂ} (h : U ≤ V) :
    holomorphicSections V →ₗ[ℂ] holomorphicSections U where
  toFun f := ⟨(U : Set ℂ).indicator f, indicator_mem_holomorphicSections h f.2⟩
  map_add' f g := Subtype.ext <| funext fun z => by by_cases hz : z ∈ U <;> simp [hz]
  map_smul' c f := Subtype.ext <| funext fun z => by by_cases hz : z ∈ U <;> simp [hz]

@[simp]
theorem coe_holomorphicRestrict {U V : Opens ℂ} (h : U ≤ V) (f : holomorphicSections V) :
    (holomorphicRestrict h f : ℂ → ℂ) = (U : Set ℂ).indicator f :=
  (rfl)

@[simp]
theorem holomorphicRestrict_self (U : Opens ℂ) (f : holomorphicSections U) :
    holomorphicRestrict le_rfl f = f :=
  Subtype.ext <| (coe_holomorphicRestrict _ f).trans <|
    indicator_eq_self.mpr fun z hz => by_contra fun hzU => hz (f.2.2 z hzU)

@[simp]
theorem holomorphicRestrict_holomorphicRestrict {U V W : Opens ℂ} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (f : holomorphicSections W) :
    holomorphicRestrict h₁ (holomorphicRestrict h₂ f) = holomorphicRestrict (h₁.trans h₂) f :=
  Subtype.ext <| by
    simp [indicator_indicator, inter_eq_left.mpr (SetLike.coe_subset_coe.mpr h₁)]

/-! ### The open sets `ℂ ∖ ℝ` and `W(U)` -/

/-- The open set `ℂ ∖ ℝ`, the union of the upper and the lower half-plane. -/
def nonRealOpen : Opens ℂ :=
  ⟨{z | z.im ≠ 0}, isOpen_ne_fun Complex.continuous_im continuous_const⟩

@[simp]
theorem mem_nonRealOpen_iff {z : ℂ} : z ∈ nonRealOpen ↔ z.im ≠ 0 :=
  Iff.rfl

/-- The non-real complex numbers are dense in `ℂ`. -/
theorem dense_nonRealOpen : Dense (nonRealOpen : Set ℂ) :=
  (dense_compl_singleton (0 : ℝ)).preimage Complex.isOpenMap_im

/-- The open set `W(U) = ℂ ∖ (ℝ ∖ U)` attached to an open set `U ⊆ ℝ`: the non-real complex
numbers together with the points of `U`. -/
def complexNeighborhood (U : Opens ℝ) : Opens ℂ :=
  nonRealOpen ⊔ ⟨Complex.re ⁻¹' U, U.isOpen.preimage Complex.continuous_re⟩

@[simp]
theorem mem_complexNeighborhood_iff {U : Opens ℝ} {z : ℂ} :
    z ∈ complexNeighborhood U ↔ z.im ≠ 0 ∨ z.re ∈ U :=
  Iff.rfl

/-- The set `W(U)` contains `ℂ ∖ ℝ`. -/
theorem nonRealOpen_le_complexNeighborhood (U : Opens ℝ) :
    nonRealOpen ≤ complexNeighborhood U :=
  le_sup_left

/-- The set `W(U)` grows with `U`. -/
theorem complexNeighborhood_mono : Monotone complexNeighborhood := fun _ _ h =>
  sup_le_sup_left (fun _ hz => h hz) _

/-! ### Functions extending across a real open set -/

/-- The holomorphic functions on `ℂ ∖ ℝ` that extend holomorphically across the open set
`U ⊆ ℝ`, that is, that are restrictions of holomorphic functions on `W(U)`. -/
def throughReal (U : Opens ℝ) : Submodule ℂ (holomorphicSections nonRealOpen) :=
  LinearMap.range (holomorphicRestrict (nonRealOpen_le_complexNeighborhood U))

/-- A holomorphic function on `ℂ ∖ ℝ` extends across `U` exactly when it agrees on `ℂ ∖ ℝ` with
a holomorphic function on `W(U)`. -/
theorem mem_throughReal_iff {U : Opens ℝ} {f : holomorphicSections nonRealOpen} :
    f ∈ throughReal U ↔
      ∃ g ∈ holomorphicSections (complexNeighborhood U), EqOn g f nonRealOpen := by
  refine ⟨fun ⟨g, hg⟩ => ⟨g, g.2, fun z hz => ?_⟩, fun ⟨g, hg, hgf⟩ => ⟨⟨g, hg⟩, ?_⟩⟩
  · rw [← hg, coe_holomorphicRestrict, indicator_of_mem hz]
  · refine Subtype.ext (funext fun z => ?_)
    by_cases hz : z ∈ nonRealOpen
    · simp [indicator_of_mem hz, hgf hz]
    · simp [indicator_of_notMem hz, f.2.2 z hz]

/-- A function extending across `V` extends across every smaller `U`. -/
theorem throughReal_antitone : Antitone throughReal := fun U V h f hf => by
  obtain ⟨g, hg, hgf⟩ := mem_throughReal_iff.mp hf
  exact mem_throughReal_iff.mpr ⟨_, indicator_mem_holomorphicSections
    (complexNeighborhood_mono h) hg, fun z hz => by
      rw [indicator_of_mem (nonRealOpen_le_complexNeighborhood U hz), hgf hz]⟩

/-- Two functions continuous on open sets containing `ℂ ∖ ℝ` that agree on `ℂ ∖ ℝ` agree on the
intersection of the two open sets: the real points there are limits of non-real ones. -/
private theorem eqOn_inf_of_eqOn_nonRealOpen {V₁ V₂ : Opens ℂ} {g₁ g₂ : ℂ → ℂ}
    (h₁ : ContinuousOn g₁ V₁) (h₂ : ContinuousOn g₂ V₂) (hV₁ : nonRealOpen ≤ V₁)
    (hV₂ : nonRealOpen ≤ V₂) (h : EqOn g₁ g₂ nonRealOpen) : EqOn g₁ g₂ (V₁ ⊓ V₂ : Opens ℂ) :=
  h.of_subset_closure (h₁.mono inter_subset_left) (h₂.mono inter_subset_right)
    (subset_inter hV₁ hV₂) (by simp [dense_nonRealOpen.closure_eq])

/-- **Extension across a union.** A holomorphic function on `ℂ ∖ ℝ` extends holomorphically
across `⋃ i, U i` exactly when it extends holomorphically across every `U i`. -/
theorem throughReal_iSup {ι : Sort*} (U : ι → Opens ℝ) :
    throughReal (⨆ i, U i) = ⨅ i, throughReal (U i) := by
  classical
  refine le_antisymm (le_iInf fun i => throughReal_antitone (le_iSup U i)) fun f hf => ?_
  rw [Submodule.mem_iInf] at hf
  choose g hg hgf using fun i => mem_throughReal_iff.mp (hf i)
  -- The glued function: `f` off the real line, and the extension `g i` at a real point of `U i`.
  let G : ℂ → ℂ := fun z =>
    if z.im = 0 then (if h : ∃ i, z.re ∈ U i then g h.choose z else 0) else (f : ℂ → ℂ) z
  -- On `W(U i)`, the glued function is the extension `g i`.
  have hG : ∀ i, EqOn G (g i) (complexNeighborhood (U i)) := by
    intro i z hz
    by_cases him : z.im ≠ 0
    · simp only [G, him, ite_false]
      exact (hgf i him).symm
    · have hre : z.re ∈ U i := (mem_complexNeighborhood_iff.mp hz).resolve_left him
      have hex : ∃ j, z.re ∈ U j := ⟨i, hre⟩
      simp only [G, not_not.mp him, hex, ite_true, dite_true]
      refine eqOn_inf_of_eqOn_nonRealOpen (hg _).1.continuousOn (hg i).1.continuousOn
        (nonRealOpen_le_complexNeighborhood _) (nonRealOpen_le_complexNeighborhood _)
        (fun w hw => (hgf _ hw).trans (hgf i hw).symm) ⟨Or.inr hex.choose_spec, hz⟩
  refine mem_throughReal_iff.mpr ⟨G, ⟨fun z hz => ?_, fun z hz => ?_⟩, fun z hz => ?_⟩
  · rcases mem_complexNeighborhood_iff.mp hz with him | hre
    · have hGf : EqOn G f nonRealOpen := fun w hw => by simp [G, mem_nonRealOpen_iff.mp hw]
      exact ((f.2.1.congr hGf).differentiableAt
        (nonRealOpen.isOpen.mem_nhds him)).differentiableWithinAt
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hre
      have hzi : z ∈ complexNeighborhood (U i) := Or.inr hi
      exact (((hg i).1.congr (hG i)).differentiableAt
        ((complexNeighborhood (U i)).isOpen.mem_nhds hzi)).differentiableWithinAt
  · have him : ¬z.im ≠ 0 := fun h => hz (Or.inl h)
    have hex : ¬∃ i, z.re ∈ U i := fun ⟨i, hi⟩ =>
      hz (Or.inr (Opens.mem_iSup.mpr ⟨i, hi⟩))
    simp only [G, not_not.mp him, hex, ite_true, dite_false]
  · simp [G, mem_nonRealOpen_iff.mp hz]

/-- A holomorphic function on `ℂ ∖ ℝ` that extends across every member of a cover of `V` extends
across `V`. -/
theorem mem_throughReal_of_le_iSup {ι : Sort*} {U : ι → Opens ℝ} {V : Opens ℝ}
    (hV : V ≤ ⨆ i, U i) {f : holomorphicSections nonRealOpen} (hf : ∀ i, f ∈ throughReal (U i)) :
    f ∈ throughReal V :=
  throughReal_antitone hV <| (throughReal_iSup U).ge (Submodule.mem_iInf _ |>.mpr hf)

/-! ### The presheaf `U ↦ O(ℂ ∖ ℝ) / O(W(U))` -/

/-- The space `O(ℂ ∖ ℝ) / O(W(U))` of one-dimensional hyperfunctions on an open set `U ⊆ ℝ`,
represented by holomorphic functions on `ℂ ∖ ℝ` modulo those extending holomorphically across
`U`. -/
abbrev OneDimBoundaryQuotient (U : Opens ℝ) :=
  holomorphicSections nonRealOpen ⧸ throughReal U

/-- Restriction of one-dimensional hyperfunctions to a smaller open set, keeping the holomorphic
representative on `ℂ ∖ ℝ`. -/
def oneDimBoundaryRestrict {U V : Opens ℝ} (h : U ≤ V) :
    OneDimBoundaryQuotient V →ₗ[ℂ] OneDimBoundaryQuotient U :=
  Submodule.mapQ (throughReal V) (throughReal U) LinearMap.id
    (by simpa using throughReal_antitone h)

@[simp]
theorem oneDimBoundaryRestrict_mk {U V : Opens ℝ} (h : U ≤ V)
    (f : holomorphicSections nonRealOpen) :
    oneDimBoundaryRestrict h (Submodule.Quotient.mk f) = Submodule.Quotient.mk f :=
  (rfl)

@[simp]
theorem oneDimBoundaryRestrict_self (U : Opens ℝ) (q : OneDimBoundaryQuotient U) :
    oneDimBoundaryRestrict le_rfl q = q :=
  Submodule.Quotient.induction_on _ q fun _ => rfl

@[simp]
theorem oneDimBoundaryRestrict_oneDimBoundaryRestrict {U V W : Opens ℝ} (h₁ : U ≤ V)
    (h₂ : V ≤ W) (q : OneDimBoundaryQuotient W) :
    oneDimBoundaryRestrict h₁ (oneDimBoundaryRestrict h₂ q) =
      oneDimBoundaryRestrict (h₁.trans h₂) q :=
  Submodule.Quotient.induction_on _ q fun _ => rfl

/-- Every one-dimensional hyperfunction on a smaller open set is the restriction of one on a
larger open set. -/
theorem oneDimBoundaryRestrict_surjective {U V : Opens ℝ} (h : U ≤ V) :
    Function.Surjective (oneDimBoundaryRestrict h) := fun q =>
  Submodule.Quotient.induction_on _ q fun f => ⟨Submodule.Quotient.mk f, rfl⟩

/-- **Locality.** A one-dimensional hyperfunction on `V` whose restrictions to the members of a
cover of `V` all vanish is zero. -/
theorem eq_zero_of_oneDimBoundaryRestrict_eq_zero {ι : Sort*} {U : ι → Opens ℝ} {V : Opens ℝ}
    (hUV : ∀ i, U i ≤ V) (hV : V ≤ ⨆ i, U i) {q : OneDimBoundaryQuotient V}
    (hq : ∀ i, oneDimBoundaryRestrict (hUV i) q = 0) : q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | H f =>
    simp only [oneDimBoundaryRestrict_mk, Submodule.Quotient.mk_eq_zero] at hq ⊢
    exact mem_throughReal_of_le_iSup hV hq

/-- **Locality.** Two one-dimensional hyperfunctions on `V` with the same restrictions to the
members of a cover of `V` are equal. -/
theorem eq_of_oneDimBoundaryRestrict_eq {ι : Sort*} {U : ι → Opens ℝ} {V : Opens ℝ}
    (hUV : ∀ i, U i ≤ V) (hV : V ≤ ⨆ i, U i) {q₁ q₂ : OneDimBoundaryQuotient V}
    (hq : ∀ i, oneDimBoundaryRestrict (hUV i) q₁ = oneDimBoundaryRestrict (hUV i) q₂) :
    q₁ = q₂ :=
  sub_eq_zero.mp <| eq_zero_of_oneDimBoundaryRestrict_eq_zero hUV hV fun i => by
    rw [map_sub, hq i, sub_self]

/-- The presheaf of complex vector spaces `U ↦ O(ℂ ∖ ℝ) / O(W(U))` on `ℝ`, whose sections are the
one-dimensional hyperfunctions. -/
-- Exposed so that the sections over `U` are, definitionally, `OneDimBoundaryQuotient U`: the
-- statements below about elements of these sections need it.
@[expose]
def oneDimBoundaryPresheaf : TopCat.Presheaf (ModuleCat ℂ) (TopCat.of ℝ) where
  obj U := ModuleCat.of ℂ (OneDimBoundaryQuotient U.unop)
  map f := ModuleCat.ofHom (oneDimBoundaryRestrict (leOfHom f.unop))
  map_id U := ModuleCat.hom_ext <| LinearMap.ext <| oneDimBoundaryRestrict_self U.unop
  map_comp _ _ := ModuleCat.hom_ext <| LinearMap.ext fun q =>
    (oneDimBoundaryRestrict_oneDimBoundaryRestrict _ _ q).symm

@[simp]
theorem oneDimBoundaryPresheaf_map_apply {U V : (Opens (TopCat.of ℝ))ᵒᵖ} (f : U ⟶ V)
    (q : OneDimBoundaryQuotient U.unop) :
    oneDimBoundaryPresheaf.map f q = oneDimBoundaryRestrict (leOfHom f.unop) q :=
  (rfl)

/-- **The presheaf of one-dimensional hyperfunctions is separated**: a section that vanishes on
the members of an open cover vanishes. -/
theorem oneDimBoundaryPresheaf_isSeparated :
    Presheaf.IsSeparated (Opens.grothendieckTopology (TopCat.of ℝ)) oneDimBoundaryPresheaf := by
  intro V S hS q₁ q₂ hq
  let ι := {p : Σ W : Opens (TopCat.of ℝ), W ⟶ V // S p.2}
  refine eq_of_oneDimBoundaryRestrict_eq (U := fun p : ι => p.1.1) (fun p => leOfHom p.1.2)
    (fun x hx => ?_) fun p => hq _ p.1.2 p.2
  obtain ⟨W, f, hf, hxW⟩ := hS x hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨W, f⟩, hf⟩, hxW⟩

end TauCeti.Hyperfunction
