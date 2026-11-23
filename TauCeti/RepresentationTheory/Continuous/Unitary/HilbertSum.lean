/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Normed.Lp.MapCLM
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.RepresentationTheory.Continuous.WithLpProd

/-!
# Hilbert direct sums of unitary representations

A family of unitary continuous representations `π i` of a monoid `G` on inner product spaces
`H i` can be summed over an arbitrary index type: `G` acts coordinatewise on the Hilbert direct sum
`lp H 2`, each operator being the direct sum `lp.mapCLM` of the uniformly bounded family
`fun i ↦ π i g`. The result is again unitary, it sends coordinate vectors to coordinate vectors,
and a vector of the sum is invariant under an element exactly when each of its coordinates is.

The direct sum `ContRepresentation.withLpProd` of two unitary representations on the Hilbert
direct sum `WithLp 2 (E × F)` is unitary as well (`ContRepresentation.IsUnitary.withLpProd`).

Direct sums of this kind assemble a single representation out of a family of witnesses, which is
how properties of representations stated with a quantifier over families (almost invariant vectors,
Kazhdan pairs, small kernels on compact groups) are reduced to a single representation. The kernel
of the direct sum is the intersection of the kernels of the summands
(`ContRepresentation.ker_toMonoidHom_hilbertSum`), and over a finite index type continuity of the
summands passes to the direct sum (`ContRepresentation.continuous_hilbertSum`).
-/

public section

noncomputable section

open scoped ENNReal Topology

namespace ContRepresentation

variable {𝕜 G ι : Type*} [RCLike 𝕜] [Monoid G] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)]

/-- The Hilbert direct sum of a family of unitary representations, acting coordinatewise on
`lp H 2`. -/
def hilbertSum (π : ∀ i, ContRepresentation 𝕜 G (H i)) (hπ : ∀ i, (π i).IsUnitary) :
    ContRepresentation 𝕜 G (lp H 2) :=
  .ofMonoidHom
    { toFun g := lp.mapCLM 2 (fun i ↦ π i g) zero_le_one fun i ↦ (hπ i).norm_le_one g
      map_one' := by ext x i; simp
      map_mul' g h := by ext x i; simp [mul_apply_eq_comp] }

variable (π : ∀ i, ContRepresentation 𝕜 G (H i)) (hπ : ∀ i, (π i).IsUnitary)

/-- The Hilbert direct sum of representations acts coordinatewise. -/
@[simp]
theorem hilbertSum_apply_apply (g : G) (x : lp H 2) (i : ι) :
    hilbertSum π hπ g x i = π i g (x i) :=
  (rfl)

/-- The Hilbert direct sum of unitary representations is unitary. -/
theorem isUnitary_hilbertSum : (hilbertSum π hπ).IsUnitary :=
  (isUnitary_iff_norm_map _).mpr fun g x ↦
    lp.norm_eq_of_forall_norm_eq fun i ↦ by simp [(hπ i).norm_map]

/-- The Hilbert direct sum of representations sends the coordinate vector `single i v` to the
coordinate vector `single i (π i g v)`. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (g : G) (i : ι) (v : H i) :
    hilbertSum π hπ g (lp.single 2 i v) = lp.single 2 i (π i g v) :=
  lp.mapCLM_single _ zero_le_one (fun i ↦ (hπ i).norm_le_one g) i v

/-- A vector of the Hilbert direct sum is fixed by `g` exactly when each of its coordinates is. -/
theorem hilbertSum_apply_eq_self_iff (g : G) (x : lp H 2) :
    hilbertSum π hπ g x = x ↔ ∀ i, π i g (x i) = x i := by
  simp [lp.ext_iff, funext_iff]

/-- A vector of the Hilbert direct sum is invariant exactly when each of its coordinates is. -/
theorem mem_invariants_hilbertSum_iff (x : lp H 2) :
    x ∈ (hilbertSum π hπ).invariants ↔ ∀ i, x i ∈ (π i).invariants := by
  simp only [mem_invariants, hilbertSum_apply_eq_self_iff]
  exact forall_comm

/-- Restricting a Hilbert direct sum along a monoid homomorphism gives the Hilbert direct sum of
the restrictions. -/
theorem restrict_hilbertSum {S : Type*} [Monoid S] (φ : S →* G) :
    (hilbertSum π hπ).restrict φ =
      hilbertSum (fun i ↦ (π i).restrict φ) fun i ↦ (hπ i).restrict φ :=
  (rfl)

/-- An element acts as the identity on the Hilbert direct sum if and only if it acts as the
identity in every summand. -/
theorem hilbertSum_apply_eq_one_iff (g : G) :
    hilbertSum π hπ g = 1 ↔ ∀ i, π i g = 1 := by
  classical
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · ext v
    simpa using congr($h (lp.single 2 i v) i)
  · ext x i
    simp [h i]

/-- Two elements act identically on the Hilbert direct sum if and only if they act identically in
every summand. -/
theorem hilbertSum_apply_eq_iff (g₁ g₂ : G) :
    hilbertSum π hπ g₁ = hilbertSum π hπ g₂ ↔ ∀ i, π i g₁ = π i g₂ := by
  classical
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · ext v
    simpa using congr($h (lp.single 2 i v) i)
  · ext x i
    simp [h i]

/-- The Hilbert direct sum is injective if and only if the summands jointly separate elements of
`G`. -/
theorem injective_hilbertSum_iff :
    Function.Injective (hilbertSum π hπ) ↔ ∀ g₁ g₂, (∀ i, π i g₁ = π i g₂) → g₁ = g₂ :=
  ⟨fun hinj _ _ h ↦ hinj ((hilbertSum_apply_eq_iff π hπ _ _).mpr h),
    fun h _ _ hgh ↦ h _ _ ((hilbertSum_apply_eq_iff π hπ _ _).mp hgh)⟩

/-- Over a finite index type, the Hilbert direct sum of continuous unitary representations is
continuous in the operator-norm topology. -/
theorem continuous_hilbertSum [TopologicalSpace G] [Finite ι]
    (hπc : ∀ i, Continuous (π i)) : Continuous (hilbertSum π hπ) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hmem : ∀ᶠ g in 𝓝 g₀, ∀ i, ‖π i g - π i g₀‖ < ε / 2 :=
    Filter.eventually_all.mpr fun i ↦ by
      simpa only [dist_eq_norm] using
        Metric.tendsto_nhds.mp (hπc i).continuousAt (ε / 2) (half_pos hε)
  refine hmem.mp (Filter.Eventually.of_forall fun g hg ↦ ?_)
  have hsub : hilbertSum π hπ g - hilbertSum π hπ g₀ =
      lp.mapCLM 2 (fun i ↦ π i g - π i g₀) (by norm_num : (0 : ℝ) ≤ 2)
        (fun i ↦ (norm_sub_le _ _).trans
          (by linarith [(hπ i).norm_le_one g, (hπ i).norm_le_one g₀])) :=
    (lp.mapCLM_sub (p := 2) (fun i ↦ π i g) (fun i ↦ π i g₀) zero_le_one
      (fun i ↦ (hπ i).norm_le_one g) zero_le_one (fun i ↦ (hπ i).norm_le_one g₀)
      (by norm_num) _).symm
  rw [dist_eq_norm, hsub, lp.norm_mapCLM]
  exact (Real.iSup_le (fun i ↦ (hg i).le) (half_pos hε).le).trans_lt (half_lt_self hε)

section Group

variable {G : Type*} [Group G] (π : ∀ i, ContRepresentation 𝕜 G (H i))
  (hπ : ∀ i, (π i).IsUnitary)

/-- The kernel of the Hilbert direct sum of group representations is the intersection of the
kernels of the summands. -/
theorem ker_toMonoidHom_hilbertSum :
    (hilbertSum π hπ).toMonoidHom.ker = ⨅ i, (π i).toMonoidHom.ker := by
  ext g
  simp [Subgroup.mem_iInf, MonoidHom.mem_ker, toMonoidHom_apply, hilbertSum_apply_eq_one_iff]

/-- The Hilbert direct sum of group representations is faithful if and only if every non-identity
element acts nontrivially in at least one summand. -/
theorem injective_hilbertSum_iff_forall_ne_one :
    Function.Injective (hilbertSum π hπ) ↔ ∀ g ≠ (1 : G), ∃ i, π i g ≠ 1 := by
  have hinj : Function.Injective (hilbertSum π hπ) ↔
      Function.Injective (hilbertSum π hπ).toMonoidHom := Iff.rfl
  rw [hinj, injective_iff_map_eq_one]
  simp only [toMonoidHom_apply, hilbertSum_apply_eq_one_iff]
  exact ⟨fun h g hg ↦ by by_contra! hc; exact hg (h g hc),
    fun h g hg ↦ by by_contra hne; obtain ⟨i, hi⟩ := h g hne; exact hi (hg i)⟩

end Group

/-- The Hilbert direct sum of two unitary representations is unitary. -/
theorem IsUnitary.withLpProd {𝕜 G E F : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {π : ContRepresentation 𝕜 G E} {ρ : ContRepresentation 𝕜 G F} (hπ : π.IsUnitary)
    (hρ : ρ.IsUnitary) : (π.withLpProd 2 ρ).IsUnitary :=
  (isUnitary_iff_norm_map _).2 fun g x ↦ by
    simp only [withLpProd_apply, WithLp.prod_norm_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
      hπ.norm_map, hρ.norm_map]

end ContRepresentation
