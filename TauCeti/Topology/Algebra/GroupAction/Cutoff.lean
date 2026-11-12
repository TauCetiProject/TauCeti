/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Cutoff functions for group actions

A cutoff function for an action of a group `G` on a space `X` is a nonnegative function
`c : X → ℝ` whose translates sum to one, `∑ᶠ g, c (g • x) = 1`, and whose topological support
meets the translates `g • K` of each compact set `K` for only finitely many `g`
(`TauCeti.MulAction.IsCutoff`). The second condition makes every such sum finite
(`TauCeti.MulAction.IsCutoff.hasFiniteSupport`), and locally finite in `x`
(`TauCeti.MulAction.IsCutoff.locallyFinite_support`), so cutoff functions can be used to average
data along the orbits of a proper action of a discrete group whose orbit space is not compact.

For the action presentation `G ⋉ X` of a discrete group, whose space of arrows is `G × X`
(`TauCeti.ActionGroupoid.arrowHomeomorph`) with source `(g, x) ↦ x` and target `(g, x) ↦ g • x`,
the sum `∑ᶠ g, c (g • x)` is the sum of `c` over the targets of the arrows with source `x`. The
finiteness condition is then the properness of the source map on the support of `c` composed with
the target (`TauCeti.MulAction.IsCutoff.isProperMap_snd`).

Each sum ranges over the whole group, so elements acting trivially are counted. In particular, for
a finite group the constant `|G|⁻¹` is a cutoff function (`TauCeti.MulAction.isCutoff_inv_card`),
whatever the kernel of the action.

## Main results

* `TauCeti.MulAction.isCutoff_div_finsum`: dividing a nonnegative function by the sum of its
  translates gives a cutoff function, as soon as each orbit meets its support and each compact set
  has finitely many translates meeting its support.
* `TauCeti.MulAction.locallyFinite_preimage_smul_tsupport`,
  `TauCeti.MulAction.locallyFinite_support_apply_smul`: under this finiteness condition the
  translates of a function have locally finite topological supports, and so locally finite
  supports.
* `TauCeti.MulAction.IsCutoff.isProperMap_snd`: the source map of the action presentation is
  proper on the support of a cutoff function composed with the target.

The smooth cutoff functions of proper actions on manifolds are constructed in
`TauCeti.Geometry.Manifold.GroupAction.Cutoff`.

## References

* N. Bourbaki, *Integration II*, Chapter VII, §2, for Bruhat functions of proper actions.
* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for cutoff functions on proper
  groupoids.
-/

public section

open Function Set Topology
open scoped Pointwise

namespace TauCeti.MulAction

variable (G : Type*) {X : Type*} [TopologicalSpace X]

section SMul

variable [SMul G X]

/-- A cutoff function for an action of `G` on `X`: a nonnegative function whose translates sum to
one at every point, and whose topological support meets the translates of each compact set by only
finitely many group elements. -/
structure IsCutoff (c : X → ℝ) : Prop where
  /-- A cutoff function is nonnegative. -/
  nonneg (x : X) : 0 ≤ c x
  /-- The translates of a cutoff function sum to one. -/
  finsum_smul_eq_one (x : X) : ∑ᶠ g : G, c (g • x) = 1
  /-- Only finitely many translates of a compact set meet the support of a cutoff function. -/
  finite_smul_inter_tsupport ⦃K : Set X⦄ (hK : IsCompact K) :
    {g : G | (g • K ∩ tsupport c).Nonempty}.Finite

variable {G}

section Finite

variable {R : Type*} [Zero R] {f : X → R}

/-- If only finitely many translates of each compact set meet the support of `f`, then each point
has only finitely many translates at which `f` is nonzero. -/
theorem hasFiniteSupport_apply_smul
    (hf : ∀ ⦃K : Set X⦄, IsCompact K → {g : G | (g • K ∩ tsupport f).Nonempty}.Finite) (x : X) :
    HasFiniteSupport fun g : G ↦ f (g • x) :=
  (hf isCompact_singleton).subset fun g hg ↦
    ⟨g • x, smul_mem_smul_set (mem_singleton x), subset_tsupport f hg⟩

/-- If only finitely many translates of each compact set meet the support of `f`, then the
preimages of the topological support of `f` under the maps `x ↦ g • x` form a locally finite
family. -/
theorem locallyFinite_preimage_smul_tsupport [WeaklyLocallyCompactSpace X]
    (hf : ∀ ⦃K : Set X⦄, IsCompact K → {g : G | (g • K ∩ tsupport f).Nonempty}.Finite) :
    LocallyFinite fun g : G ↦ (g • ·) ⁻¹' tsupport f := fun x ↦ by
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  exact ⟨K, hKx, (hf hK).subset fun g ⟨y, hy, hyK⟩ ↦ ⟨g • y, smul_mem_smul_set hyK, hy⟩⟩

/-- If only finitely many translates of each compact set meet the support of `f`, then the
supports of the translates `x ↦ f (g • x)` form a locally finite family. -/
theorem locallyFinite_support_apply_smul [WeaklyLocallyCompactSpace X]
    (hf : ∀ ⦃K : Set X⦄, IsCompact K → {g : G | (g • K ∩ tsupport f).Nonempty}.Finite) :
    LocallyFinite fun g : G ↦ support fun x ↦ f (g • x) :=
  (locallyFinite_preimage_smul_tsupport hf).subset fun _ _ hx ↦ subset_tsupport f hx

end Finite

/-- If `f` is nonnegative, nonzero somewhere on the orbit of `x`, and only finitely many translates
of each compact set meet its support, then the sum of the translates of `f` at `x` is positive. -/
theorem finsum_apply_smul_pos {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedCancelAddMonoid R] {f : X → R} (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ ⦃K : Set X⦄, IsCompact K → {g : G | (g • K ∩ tsupport f).Nonempty}.Finite) {x : X}
    (hx : ∃ g : G, f (g • x) ≠ 0) : 0 < ∑ᶠ g : G, f (g • x) := by
  obtain ⟨g, hg⟩ := hx
  exact finsum_pos (fun _ ↦ hf0 _) ⟨g, (hf0 _).lt_of_ne' hg⟩ (hasFiniteSupport_apply_smul hf x)

/-- For a finite nonempty `G`, such as a finite group, the constant function `|G|⁻¹` is a cutoff
function. Every element is counted, including those acting trivially. -/
theorem isCutoff_inv_card [Fintype G] [Nonempty G] :
    IsCutoff G fun _ : X ↦ (Fintype.card G : ℝ)⁻¹ where
  nonneg _ := inv_nonneg.2 (Nat.cast_nonneg _)
  finsum_smul_eq_one _ := by
    simp [finsum_eq_sum_of_fintype, Fintype.card_ne_zero]
  finite_smul_inter_tsupport _ _ := toFinite _

namespace IsCutoff

variable {c : X → ℝ}

/-- The translates of a cutoff function at a point are nonzero for only finitely many group
elements. -/
theorem hasFiniteSupport (hc : IsCutoff G c) (x : X) : HasFiniteSupport fun g : G ↦ c (g • x) :=
  hasFiniteSupport_apply_smul hc.finite_smul_inter_tsupport x

/-- The supports of the translates `x ↦ c (g • x)` of a cutoff function form a locally finite
family. -/
theorem locallyFinite_support [WeaklyLocallyCompactSpace X] (hc : IsCutoff G c) :
    LocallyFinite fun g : G ↦ support fun x ↦ c (g • x) :=
  locallyFinite_support_apply_smul hc.finite_smul_inter_tsupport

/-- The source map `(g, x) ↦ x` of the action presentation of a discrete group is proper on the
support of a cutoff function composed with the target map `(g, x) ↦ g • x`. -/
theorem isProperMap_snd [TopologicalSpace G] [DiscreteTopology G] [ContinuousConstSMul G X]
    [T2Space X] [CompactlyCoherentSpace X] (hc : IsCutoff G c) :
    IsProperMap fun p : tsupport (fun p : G × X ↦ c (p.1 • p.2)) ↦ (p : G × X).2 := by
  have hact : Continuous fun p : G × X ↦ p.1 • p.2 :=
    continuous_prod_of_discrete_left.2 fun g ↦ continuous_const_smul g
  have hsupp : tsupport (fun p : G × X ↦ c (p.1 • p.2)) ⊆ (fun p ↦ p.1 • p.2) ⁻¹' tsupport c :=
    closure_minimal (fun p hp ↦ subset_tsupport c hp) ((isClosed_tsupport c).preimage hact)
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨continuous_snd.comp continuous_subtype_val, fun K hK ↦ ?_⟩
  have hpre : (fun p : tsupport (fun p : G × X ↦ c (p.1 • p.2)) ↦ (p : G × X).2) ⁻¹' K =
      Subtype.val ⁻¹' ({g : G | (g • K ∩ tsupport c).Nonempty} ×ˢ K) := by
    ext ⟨⟨g, x⟩, hp⟩
    refine ⟨fun hx ↦ ⟨⟨g • x, smul_mem_smul_set hx, hsupp hp⟩, hx⟩, fun h ↦ h.2⟩
  rw [hpre]
  exact (isClosed_tsupport _).isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hc.finite_smul_inter_tsupport hK).isCompact.prod hK)

end IsCutoff

end SMul

variable {G}

/-- Dividing a nonnegative function by the sum of its translates gives a cutoff function, provided
every orbit meets the locus where the function is nonzero and only finitely many translates of each
compact set meet its support. -/
theorem isCutoff_div_finsum [Group G] [MulAction G X] {β : X → ℝ} (hβ : ∀ x, 0 ≤ β x)
    (hfin : ∀ ⦃K : Set X⦄, IsCompact K → {g : G | (g • K ∩ tsupport β).Nonempty}.Finite)
    (hpos : ∀ x, ∃ g : G, β (g • x) ≠ 0) :
    IsCutoff G fun x ↦ β x / ∑ᶠ g : G, β (g • x) := by
  have hsum (x : X) : 0 < ∑ᶠ g : G, β (g • x) := finsum_apply_smul_pos hβ hfin (hpos x)
  have hinv (h : G) (x : X) : ∑ᶠ g : G, β (g • h • x) = ∑ᶠ g : G, β (g • x) := by
    simpa only [Equiv.coe_mulRight, mul_smul] using
      finsum_comp_equiv (Equiv.mulRight h) (f := fun g ↦ β (g • x))
  refine ⟨fun x ↦ div_nonneg (hβ x) (hsum x).le, fun x ↦ ?_, fun _ hK ↦ (hfin hK).subset ?_⟩
  · simp only [hinv, div_eq_mul_inv]
    rw [← finsum_mul, mul_inv_cancel₀ (hsum x).ne']
  · rintro g ⟨y, hyK, hy⟩
    refine ⟨y, hyK, closure_mono ?_ hy⟩
    rw [support_div]
    exact inter_subset_left

end TauCeti.MulAction
