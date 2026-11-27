/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CrossedCocycle.Splitting
public import TauCeti.Topology.Algebra.Group.LocallyConstant
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The wild cutoff of a crossed cocycle

Let a group `Γ` map to a group `Q` by `η : Γ →* Q`, let `Q` act on a group `H` by
`β : Q →* MulAut H`, and let `c` be a crossed cocycle for `β ∘ η`, with lift
`γ ↦ (c γ, η γ) : Γ →* H ⋊[β] Q`. For a subgroup `P` of `Γ`, the **wild cutoff** of `c` in `P` is
the intersection of `P` with the kernel of this lift: the elements of `P` at which both `c` and `η`
are trivial.

For a Langlands parameter `c` of a Weil group `Γ = W_E`, with `P` its wild inertia subgroup, the
wild cutoff is the subgroup of wild inertia on which the parameter is trivial. It lies in
`P ⊓ ker η`, kills `c`, and contains every subgroup of `P ⊓ ker η` killing `c`, so it is the
largest such subgroup (`TauCeti.CrossedCocycle.le_wildCutoff_iff`). It is normal when `P` is, and
it lies in the kernel of the action `β ∘ η` (`TauCeti.CrossedCocycle.wildCutoff_le_ker`), so
both the action and the cocycle are trivial on it. Unlike the identity fibre `{γ | c γ = 1}` of
the cocycle alone, it is unchanged by gauge (`TauCeti.CrossedCocycle.wildCutoff_smul`), so it
depends only on the gauge class. It is compatible with pulling back along a homomorphism
(`TauCeti.CrossedCocycle.comap_wildCutoff`).

Both conditions in its definition matter. For `Γ = Q`, `η` the identity and the unit cocycle, the
cutoff is `P ⊓ ker η = ⊥`, even for the trivial action: replacing `ker η` by the kernel of the
action would be wrong. For trivial `Q` and a cocycle injective on `P`, the cutoff is again `⊥`,
so it is not `P ⊓ ker η` either.

When `c` is continuous on `P` with finite image there, `η` is continuous on `P` and `Q` is
discrete, the wild cutoff is open in `P` (`TauCeti.CrossedCocycle.isOpen_wildCutoff_subgroupOf`).
Conversely, for compact `P` in a topological group, a cutoff open in `P` is the open kernel of the
lift restricted to `P`, which therefore has finite range, so `c` has finite image on `P`
(`TauCeti.CrossedCocycle.finite_image_of_isOpen_wildCutoff_subgroupOf`, from
`MonoidHom.finite_range_of_isOpen_ker`). Thus the wild cutoff
of a parameter continuous on compact wild inertia is open in wild inertia exactly when the
parameter has finite image there (`TauCeti.CrossedCocycle.isOpen_wildCutoff_subgroupOf_iff`).
The analogous criterion for continuous homomorphisms on compact groups is
`MonoidHom.isOpen_ker_iff_finite_range`.

## Main definitions

* `TauCeti.CrossedCocycle.wildCutoff`: the wild cutoff `P ⊓ ker (γ ↦ (c γ, η γ))`.

## Main results

* `TauCeti.CrossedCocycle.mem_wildCutoff`: `γ` lies in the wild cutoff exactly when `γ ∈ P`,
  `c γ = 1` and `η γ = 1`.
* `TauCeti.CrossedCocycle.le_wildCutoff_iff`: the wild cutoff is the largest subgroup of
  `P ⊓ ker η` on which `c` is trivial.
* `TauCeti.CrossedCocycle.wildCutoff_smul`: the wild cutoff is gauge invariant.
* `TauCeti.CrossedCocycle.comap_wildCutoff`: the wild cutoff of a pulled-back cocycle in a
  pulled-back subgroup is the pullback of the wild cutoff.
* `TauCeti.CrossedCocycle.isOpen_wildCutoff_subgroupOf`: the wild cutoff of a continuous
  cocycle with finite image on `P` is open in `P`.
* `TauCeti.CrossedCocycle.isOpen_wildCutoff_subgroupOf_iff`: for compact `P`, the wild cutoff of
  a continuous cocycle is open in `P` exactly when the cocycle has finite image on `P`.

## References

* L. Fargues, P. Scholze, *Geometrization of the local Langlands correspondence*, Remark VIII.1.2
  and the proof of Theorem VIII.1.3.
* J.-F. Dat, D. Helm, R. Kurinczuk, G. Moss, *Moduli of Langlands parameters*, §1.2 and §2.1.
-/

public section

namespace TauCeti

namespace CrossedCocycle

open SemidirectProduct

variable {Γ H Q : Type*} [Group Γ] [Group H] [Group Q] {β : Q →* MulAut H} {η : Γ →* Q}

/-- The **wild cutoff** of a crossed cocycle `c` for `β ∘ η` in a subgroup `P`: the intersection
of `P` with the kernel of the lift `γ ↦ (c γ, η γ)` of `η`, that is, the elements of `P` at which
both `c` and `η` are trivial (`TauCeti.CrossedCocycle.mem_wildCutoff`). -/
def wildCutoff (c : CrossedCocycle (β.comp η)) (P : Subgroup Γ) : Subgroup Γ :=
  P ⊓ c.toSemidirectHom.ker

variable {c : CrossedCocycle (β.comp η)} {P P' : Subgroup Γ} {γ : Γ}

theorem wildCutoff_def (c : CrossedCocycle (β.comp η)) (P : Subgroup Γ) :
    c.wildCutoff P = P ⊓ c.toSemidirectHom.ker :=
  (rfl)

@[simp]
theorem mem_wildCutoff : γ ∈ c.wildCutoff P ↔ γ ∈ P ∧ c γ = 1 ∧ η γ = 1 := by
  simp [wildCutoff_def, SemidirectProduct.ext_iff]

/-- The wild cutoff lies in `P ⊓ ker η`. -/
theorem wildCutoff_le : c.wildCutoff P ≤ P ⊓ η.ker :=
  fun _ hγ ↦ ⟨(mem_wildCutoff.mp hγ).1, (mem_wildCutoff.mp hγ).2.2⟩

theorem wildCutoff_le_left : c.wildCutoff P ≤ P :=
  inf_le_left

/-- The wild cutoff lies in the kernel of the action `β ∘ η`. -/
theorem wildCutoff_le_ker : c.wildCutoff P ≤ (β.comp η).ker :=
  fun _ hγ ↦ by simp [(mem_wildCutoff.mp hγ).2.2]

/-- A crossed cocycle is trivial on its wild cutoff. -/
theorem apply_eq_one_of_mem_wildCutoff (hγ : γ ∈ c.wildCutoff P) : c γ = 1 :=
  (mem_wildCutoff.mp hγ).2.1

/-- The wild cutoff is the largest subgroup of `P ⊓ ker η` on which `c` is trivial. -/
theorem le_wildCutoff_iff {U : Subgroup Γ} :
    U ≤ c.wildCutoff P ↔ U ≤ P ⊓ η.ker ∧ ∀ γ ∈ U, c γ = 1 := by
  refine ⟨fun h ↦ ⟨h.trans wildCutoff_le, fun _ hγ ↦ apply_eq_one_of_mem_wildCutoff (h hγ)⟩,
    fun ⟨hU, hc⟩ γ hγ ↦ mem_wildCutoff.mpr ⟨(hU hγ).1, hc γ hγ, (hU hγ).2⟩⟩

/-- The wild cutoff in a normal subgroup is normal. -/
instance [P.Normal] : (c.wildCutoff P).Normal :=
  inferInstanceAs (P ⊓ c.toSemidirectHom.ker).Normal

theorem wildCutoff_mono (h : P ≤ P') : c.wildCutoff P ≤ c.wildCutoff P' :=
  inf_le_inf_right _ h

/-- The wild cutoff of the unit cocycle is `P ⊓ ker η`. -/
@[simp]
theorem wildCutoff_one : (1 : CrossedCocycle (β.comp η)).wildCutoff P = P ⊓ η.ker := by
  ext
  simp

/-- The wild cutoff is unchanged by gauge. -/
@[simp]
theorem wildCutoff_smul (h : H) (c : CrossedCocycle (β.comp η)) (P : Subgroup Γ) :
    (h • c).wildCutoff P = c.wildCutoff P := by
  ext γ
  simp only [mem_wildCutoff, smul_apply, MonoidHom.comp_apply]
  -- Where `η γ = 1` the action is trivial, so gauge conjugates `c γ` by `h`.
  constructor <;> rintro ⟨hγ, hc, hη⟩ <;> simp_all

/-- Pulling back along `f : Δ →* Γ`: if `c'` is the crossed cocycle `c ∘ f` for the pulled-back
action, then its wild cutoff in `P.comap f` is the pullback of the wild cutoff of `c` in `P`. -/
theorem comap_wildCutoff {Δ : Type*} [Group Δ] (f : Δ →* Γ)
    {c' : CrossedCocycle (β.comp (η.comp f))} (hc' : ∀ δ, c' δ = c (f δ)) :
    (c.wildCutoff P).comap f = c'.wildCutoff (P.comap f) := by
  ext
  simp [hc']

section Topology

variable [TopologicalSpace Γ]

/-- If `c` is continuous on `P` with finite image there and `η` is continuous on `P` with values in
the discrete group `Q`, then the wild cutoff of `c` is open in `P`. -/
theorem isOpen_wildCutoff_subgroupOf [TopologicalSpace H] [T1Space H] [TopologicalSpace Q]
    [DiscreteTopology Q] (hc : ContinuousOn c P) (hfin : (c '' P).Finite)
    (hη : ContinuousOn η P) : IsOpen ((c.wildCutoff P).subgroupOf P : Set P) := by
  -- The restriction of `c` to `P` is continuous with finite range, hence locally constant.
  have hc₁ : IsOpen {p : P | c p = 1} :=
    (IsLocallyConstant.of_continuous_of_finite_range hc.domRestrict
      (by rwa [Set.range_domRestrict])).isOpen_fiber 1
  have hη₁ : IsOpen {p : P | η p = 1} := hη.domRestrict.isOpen_preimage {1} (isOpen_discrete _)
  have hcut : ((c.wildCutoff P).subgroupOf P : Set P) = {p : P | c p = 1} ∩ {p : P | η p = 1} := by
    ext p
    simp [Subgroup.mem_subgroupOf]
  rw [hcut]
  exact hc₁.inter hη₁

/-- If `P` is compact and the wild cutoff of `c` is open in `P`, then `c` has finite image on `P`:
the wild cutoff in `P` is the kernel of the lift `γ ↦ (c γ, η γ)` restricted to `P`, so that
restriction has finite range. -/
theorem finite_image_of_isOpen_wildCutoff_subgroupOf [IsTopologicalGroup Γ]
    (hP : IsCompact (P : Set Γ)) (h : IsOpen ((c.wildCutoff P).subgroupOf P : Set P)) :
    (c '' P).Finite := by
  have := isCompact_iff_compactSpace.mp hP
  have hker : (c.toSemidirectHom.comp P.subtype).ker = (c.wildCutoff P).subgroupOf P := by
    ext p
    simp [Subgroup.mem_subgroupOf, SemidirectProduct.ext_iff]
  have hfin := (c.toSemidirectHom.comp P.subtype).finite_range_of_isOpen_ker (hker ▸ h)
  refine (hfin.image SemidirectProduct.left).subset ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact ⟨_, ⟨⟨γ, hγ⟩, rfl⟩, by simp⟩

/-- For compact `P` in a topological group, a cocycle continuous on `P`, and `η` continuous on `P`
with values in the discrete group `Q`, the wild cutoff of `c` is open in `P` exactly when `c` has
finite image on `P`. -/
theorem isOpen_wildCutoff_subgroupOf_iff [IsTopologicalGroup Γ] [TopologicalSpace H] [T1Space H]
    [TopologicalSpace Q] [DiscreteTopology Q] (hP : IsCompact (P : Set Γ)) (hc : ContinuousOn c P)
    (hη : ContinuousOn η P) :
    IsOpen ((c.wildCutoff P).subgroupOf P : Set P) ↔ (c '' P).Finite :=
  ⟨finite_image_of_isOpen_wildCutoff_subgroupOf hP,
    fun hfin ↦ isOpen_wildCutoff_subgroupOf hc hfin hη⟩

end Topology

end CrossedCocycle

end TauCeti
