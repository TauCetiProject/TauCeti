/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.EssentialSubspace
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.LocallyConvex.WeakOperatorTopology
public import TauCeti.Analysis.VonNeumannAlgebra.Adjoin
public import TauCeti.Analysis.VonNeumannAlgebra.Density
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Nonunital star subalgebras of operators, essential subspaces, and operator closures

A nonunital star subalgebra `A` of bounded operators on a Hilbert space `H` need not contain the
identity operator on `H`, and its raw double commutant `A''` always contains `1` even when every
operator in `A` vanishes on a nontrivial subspace. Separating the common annihilator from the
essential subspace resolves this discrepancy.

The essential subspace `A.essentialSubspace`, its identification with the orthogonal complement of
the common annihilator `⨅ a ∈ A, ker a`, and the nondegenerate compression
`A.restrictEssentialSubspace` with isometric isomorphism `A.restrictEssentialSubspaceEquiv` are
developed in `TauCeti.Analysis.InnerProductSpace.EssentialSubspace`. The general nonunital von
Neumann density theorems
(`NonUnitalStarSubalgebra.apply_mem_closure_of_mem_centralizer_centralizer` and
`NonUnitalStarSubalgebra.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer`) are
proved in `TauCeti.Analysis.VonNeumannAlgebra.Density`. Here we develop the commutant,
double-commutant, essential-projection approximation, and strong/weak operator closure theory on
top of those results.

Specializing nonunital density to `A.essentialSubspace.starProjection` approximates the essential
projection on one or finitely many vectors
(`NonUnitalStarSubalgebra.starProjection_essentialSubspace_apply_mem_closure`,
`NonUnitalStarSubalgebra.exists_forall_norm_starProjection_essentialSubspace_sub_apply_lt`).

Consequently:

* On `A.essentialSubspace`, both the strong and weak operator closures of
  `A.restrictEssentialSubspace` equal its unital double commutant `(A.restrictEssentialSubspace)''`
  (`closure_image_toPointwiseConvergenceCLM_restrictEssentialSubspace`,
  `closure_image_ofCLM_restrictEssentialSubspace`), packaging over `ℂ` into a concrete
  `VonNeumannAlgebra A.essentialSubspace` (`NonUnitalStarSubalgebra.essentialVonNeumannAlgebra`).
* On `H`, both the strong and weak operator closures of `A` equal the supported algebra
  `{x ∈ A'' | ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} =
  A.essentialSubspace.extendByZero '' (A.restrictEssentialSubspace)''`, with two-sided identity
  `A.essentialSubspace.starProjection` (`closure_image_toPointwiseConvergenceCLM`,
  `closure_image_ofCLM`).
* By contrast, the full double commutant `A''` splits as
  `A.essentialSubspace.extendByZero '' (A.restrictEssentialSubspace)'' +
  𝕜 • A.essentialSubspaceᗮ.starProjection` (`mem_centralizer_centralizer_iff`, and over `ℂ`
  `coe_vonNeumannAlgebraAdjoin`), adjoining scalar multiples of the identity on the annihilator;
  thus `1` belongs to the strong or weak operator closure of `A` (and those closures equal `A''`)
  if and only if `A.essentialSubspace = ⊤`.

## References

* Jacques Dixmier, *Von Neumann Algebras*, Part I, Chapter I, Section 3, Corollary 1.
* Richard V. Kadison and John R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Section 5.3, Remark 5.3.2.
-/

public section

noncomputable section

open scoped InnerProductSpace Topology

namespace NonUnitalStarSubalgebra

section Commutant

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the commutant of `A`. -/
theorem starProjection_essentialSubspace_mem_centralizer
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace.starProjection ∈ (A : Set (H →L[𝕜] H)).centralizer :=
  fun _ ha => (A.mul_starProjection_essentialSubspace ha).trans
    (A.starProjection_essentialSubspace_mul ha).symm

/-- Every operator on `A.essentialSubspaceᗮ` extended by zero on `A.essentialSubspace` belongs to
the commutant of `A`. -/
theorem extendByZero_orthogonal_mem_centralizer (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H))
    (Q : A.essentialSubspaceᗮ →L[𝕜] A.essentialSubspaceᗮ) :
    A.essentialSubspaceᗮ.extendByZero Q ∈ (A : Set (H →L[𝕜] H)).centralizer := by
  rw [← A.image_extendByZero_restrictEssentialSubspace]
  rintro _ ⟨S, -, rfl⟩
  exact A.essentialSubspace.commute_extendByZero_extendByZero_orthogonal S Q

/-- `A.essentialSubspace` reduces every operator in the commutant of `A`. -/
theorem isReducing_essentialSubspace_of_mem_centralizer {y : H →L[𝕜] H}
    (hy : y ∈ (A : Set (H →L[𝕜] H)).centralizer) :
    A.essentialSubspace.IsReducing (y : Module.End 𝕜 H) := by
  refine (A.essentialSubspace.isReducing_iff _).2 ⟨?_, ?_⟩
  · rw [Module.End.mem_invtSubmodule]
    refine (A.essentialSubspace_le_iff
      (A.isClosed_essentialSubspace.preimage y.continuous)).2 fun a ha ξ => ?_
    have hcomm : a (y ξ) = y (a ξ) := by
      simpa only [_root_.mul_apply_eq_comp] using congrArg (fun T : H →L[𝕜] H => T ξ) (hy a ha)
    simpa only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, ← hcomm] using
      A.apply_mem_essentialSubspace ha (y ξ)
  · intro ξ hξ
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, A.mem_orthogonal_essentialSubspace_iff]
    intro a ha
    have hcomm := congrArg (fun T : H →L[𝕜] H => T ξ) (hy a ha)
    simpa only [_root_.mul_apply_eq_comp,
      A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha, map_zero] using hcomm

/-- Every operator in the commutant of `A` commutes with `A.essentialSubspace.starProjection`. -/
theorem commute_starProjection_essentialSubspace_of_mem_centralizer {y : H →L[𝕜] H}
    (hy : y ∈ (A : Set (H →L[𝕜] H)).centralizer) :
    Commute A.essentialSubspace.starProjection y :=
  Submodule.isReducing_coe_iff_commute_starProjection.1
    (A.isReducing_essentialSubspace_of_mem_centralizer hy)

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the double commutant `A''`. -/
theorem starProjection_essentialSubspace_mem_centralizer_centralizer
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace.starProjection ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer :=
  fun _ hy => (A.commute_starProjection_essentialSubspace_of_mem_centralizer hy).symm.eq

end Commutant

section DoubleCommutant

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}

/-- `A.essentialSubspace.extendByZero R` commutes with `A` on `H` if and only if `R` commutes with
`A.restrictEssentialSubspace` on `A.essentialSubspace`. -/
theorem extendByZero_mem_centralizer_iff
    {R : A.essentialSubspace →L[𝕜] A.essentialSubspace} :
    A.essentialSubspace.extendByZero R ∈ (A : Set (H →L[𝕜] H)).centralizer ↔
      R ∈ (A.restrictEssentialSubspace : Set _).centralizer := by
  rw [← A.image_extendByZero_restrictEssentialSubspace]
  simp only [Set.mem_centralizer_iff, Set.forall_mem_image, ← map_mul,
    A.essentialSubspace.extendByZero_injective.eq_iff]

/-- Compressing an element of `A'` to `A.essentialSubspace` yields an element of
`(A.restrictEssentialSubspace)'`. -/
theorem orthogonalProjectionOnto_comp_mem_centralizer_restrictEssentialSubspace {y : H →L[𝕜] H}
    (hy : y ∈ (A : Set (H →L[𝕜] H)).centralizer) :
    A.essentialSubspace.orthogonalProjectionOnto ∘L y ∘L A.essentialSubspace.subtypeL ∈
      (A.restrictEssentialSubspace : Set _).centralizer := by
  intro S hS
  have hcomm : Commute (A.essentialSubspace.extendByZero S) y :=
    hy _ (A.mem_restrictEssentialSubspace.1 hS)
  exact (A.essentialSubspace.commute_extendByZero_iff_of_commute
    (A.commute_starProjection_essentialSubspace_of_mem_centralizer hy) S).1 hcomm

/-- `A.essentialSubspace.extendByZero S` belongs to `A''` on `H` if and only if `S` belongs to
`(A.restrictEssentialSubspace)''` on `A.essentialSubspace`. -/
theorem extendByZero_mem_centralizer_centralizer_iff
    {S : A.essentialSubspace →L[𝕜] A.essentialSubspace} :
    A.essentialSubspace.extendByZero S ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      S ∈ (A.restrictEssentialSubspace : Set _).centralizer.centralizer := by
  refine ⟨fun hS R hR => ?_, fun hS y hy => ?_⟩
  · have hcomm : Commute (A.essentialSubspace.extendByZero R)
        (A.essentialSubspace.extendByZero S) :=
      hS _ (A.extendByZero_mem_centralizer_iff.2 hR)
    exact A.essentialSubspace.extendByZero_injective (by simpa only [map_mul] using hcomm.eq)
  · have hy_comm := A.commute_starProjection_essentialSubspace_of_mem_centralizer hy
    have hSR : Commute S
        (A.essentialSubspace.orthogonalProjectionOnto ∘L y ∘L A.essentialSubspace.subtypeL) :=
      (hS _ (A.orthogonalProjectionOnto_comp_mem_centralizer_restrictEssentialSubspace hy)).symm
    exact ((A.essentialSubspace.commute_extendByZero_iff_of_commute hy_comm S).2 hSR).symm.eq

/-- Compressing an element of `A''` to `A.essentialSubspace` yields an element of
`(A.restrictEssentialSubspace)''`. -/
theorem orthogonalProjectionOnto_comp_mem_centralizer_centralizer_restrictEssentialSubspace
    {x : H →L[𝕜] H} (hx : x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer) :
    A.essentialSubspace.orthogonalProjectionOnto ∘L x ∘L A.essentialSubspace.subtypeL ∈
      (A.restrictEssentialSubspace : Set _).centralizer.centralizer := by
  have hx_comm : Commute A.essentialSubspace.starProjection x :=
    hx _ A.starProjection_essentialSubspace_mem_centralizer
  intro R hR
  have hRx : Commute (A.essentialSubspace.extendByZero R) x :=
    hx _ (A.extendByZero_mem_centralizer_iff.2 hR)
  exact (A.essentialSubspace.commute_extendByZero_iff_of_commute hx_comm R).1 hRx

/-- **Decomposition of the double commutant of a nonunital star subalgebra.** Every operator in
`A''` decomposes into an element of `(A.restrictEssentialSubspace)''` extended by zero on
`A.essentialSubspaceᗮ` plus a scalar multiple of the orthogonal projection onto the common
annihilator `A.essentialSubspaceᗮ`. -/
theorem mem_centralizer_centralizer_iff {x : H →L[𝕜] H} :
    x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      ∃ S ∈ (A.restrictEssentialSubspace : Set _).centralizer.centralizer,
        ∃ c : 𝕜, x = A.essentialSubspace.extendByZero S +
          c • A.essentialSubspaceᗮ.starProjection := by
  refine ⟨fun hx => ?_, ?_⟩
  · have hx_comm : Commute A.essentialSubspace.starProjection x :=
      hx _ A.starProjection_essentialSubspace_mem_centralizer
    have hx_orth_comm : Commute A.essentialSubspaceᗮ.starProjection x :=
      A.essentialSubspace.commute_starProjection_orthogonal_iff.2 hx_comm
    set x_orth : A.essentialSubspaceᗮ →L[𝕜] A.essentialSubspaceᗮ :=
      A.essentialSubspaceᗮ.orthogonalProjectionOnto ∘L x ∘L A.essentialSubspaceᗮ.subtypeL with
      hx_orth_def
    -- `x_orth` commutes with every bounded operator on `A.essentialSubspaceᗮ`, so it lies in the
    -- center of `B(A.essentialSubspaceᗮ)` and is therefore a scalar multiple of `1`.
    have hx_center : x_orth ∈ Subalgebra.center 𝕜
        (A.essentialSubspaceᗮ →L[𝕜] A.essentialSubspaceᗮ) := by
      rw [Subalgebra.mem_center_iff]
      intro Q
      have hQx : Commute (A.essentialSubspaceᗮ.extendByZero Q) x :=
        hx _ (A.extendByZero_orthogonal_mem_centralizer Q)
      exact (A.essentialSubspaceᗮ.commute_extendByZero_iff_of_commute hx_orth_comm Q).1 hQx
    obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff (K := 𝕜)).1 hx_center
    have hx_orth_eq : x_orth = c • 1 := by
      rw [hc, Algebra.algebraMap_eq_smul_one]
    refine ⟨_,
      A.orthogonalProjectionOnto_comp_mem_centralizer_centralizer_restrictEssentialSubspace hx,
      c, ?_⟩
    conv_lhs =>
      rw [A.essentialSubspace.eq_extendByZero_add_extendByZero_orthogonal_of_commute hx_comm]
    rw [← hx_orth_def, hx_orth_eq, map_smul, Submodule.extendByZero_one]
  · rintro ⟨S, hS, c, rfl⟩
    have hS' : A.essentialSubspace.extendByZero S ∈
        (A : Set (H →L[𝕜] H)).centralizer.centralizer :=
      A.extendByZero_mem_centralizer_centralizer_iff.2 hS
    have hp_orth : A.essentialSubspaceᗮ.starProjection ∈
        (A : Set (H →L[𝕜] H)).centralizer.centralizer :=
      fun _ hy => (A.essentialSubspace.commute_starProjection_orthogonal_iff.2
        (A.commute_starProjection_essentialSubspace_of_mem_centralizer hy)).symm.eq
    exact Set.add_mem_centralizer hS' (Set.smul_mem_centralizer c hp_orth)

/-- Extending `(A.restrictEssentialSubspace)''` by zero on `A.essentialSubspaceᗮ` cuts out
precisely the operators in `A''` that vanish on the common annihilator `A.essentialSubspaceᗮ`. -/
theorem image_extendByZero_centralizer_centralizer (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    A.essentialSubspace.extendByZero ''
      (A.restrictEssentialSubspace : Set _).centralizer.centralizer =
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  ext x
  refine ⟨?_, fun ⟨hx, hker⟩ => ?_⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨A.extendByZero_mem_centralizer_centralizer_iff.2 hS, fun _ hξ =>
      A.essentialSubspace.extendByZero_apply_of_mem_orthogonal S hξ⟩
  · let U := A.essentialSubspace
    have hx_comm : Commute U.starProjection x :=
      hx _ A.starProjection_essentialSubspace_mem_centralizer
    refine ⟨U.orthogonalProjectionOnto ∘L x ∘L U.subtypeL,
      A.orthogonalProjectionOnto_comp_mem_centralizer_centralizer_restrictEssentialSubspace hx, ?_⟩
    rw [
      U.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection_of_commute
        hx_comm, U.mul_starProjection_eq_self hker]

end DoubleCommutant

section Density

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- For every vector `v : H`, `A.essentialSubspace.starProjection v` lies in the closure of the
orbit `A v`. -/
theorem starProjection_essentialSubspace_apply_mem_closure
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) (v : H) :
    A.essentialSubspace.starProjection v ∈ closure ((fun a : H →L[𝕜] H => a v) '' A) :=
  A.apply_mem_closure_of_mem_centralizer_centralizer
    A.starProjection_essentialSubspace_mem_centralizer_centralizer
    (fun _ hξ => A.essentialSubspace.starProjection_apply_eq_zero_iff.2 hξ) v

/-- The orthogonal projection onto `A.essentialSubspace` can be approximated simultaneously on any
finite family of vectors in `H` by elements of `A`. -/
theorem exists_forall_norm_starProjection_essentialSubspace_sub_apply_lt
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) {ι : Type*} [Finite ι]
    (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ i, ‖A.essentialSubspace.starProjection (v i) - a (v i)‖ < ε :=
  A.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    A.starProjection_essentialSubspace_mem_centralizer_centralizer
    (fun _ hξ => A.essentialSubspace.starProjection_apply_eq_zero_iff.2 hξ) v hε

end Density

section Closures

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Every operator in `A` lies in `A''` and annihilates `A.essentialSubspaceᗮ`. -/
private theorem subset_supported (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    (A : Set (H →L[𝕜] H)) ⊆
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} :=
  fun _ ha => ⟨Set.subset_centralizer_centralizer ha, fun _ hξ =>
    A.apply_eq_zero_of_mem_orthogonal_essentialSubspace hξ ha⟩

/-- The set of operators in `A''` vanishing on `A.essentialSubspaceᗮ` is weak-operator closed. -/
private theorem isClosed_image_ofCLM_supported
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM ''
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0}) := by
  have himg : ContinuousLinearMapWOT.ofCLM ''
      {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
        ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} =
      (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)).centralizer.centralizer) ∩
        ⋂ ξ ∈ (A.essentialSubspaceᗮ : Set H), ⋂ ψ : StrongDual 𝕜 H,
          {T : H →WOT[𝕜] H | ψ (T ξ) = 0} := by
    ext T
    obtain ⟨x, rfl⟩ := ContinuousLinearMapWOT.ofCLM_surjective T
    simp only [Set.mem_inter_iff, ContinuousLinearMapWOT.ofCLM_injective.mem_set_image,
      Set.mem_iInter, SetLike.mem_coe, Set.mem_ofPred, ContinuousLinearMapWOT.ofCLM_apply]
    exact and_congr_right fun _ => forall₂_congr fun ξ _ =>
      ⟨fun h ψ => by rw [h, map_zero],
        fun h => ext_inner_left 𝕜 fun v => by simpa using h (innerSL 𝕜 v)⟩
  rw [himg]
  exact ((A : Set (H →L[𝕜] H)).centralizer.isClosed_image_ofCLM_centralizer).inter <|
    isClosed_biInter fun ξ _ => isClosed_iInter fun ψ =>
      isClosed_eq (ContinuousLinearMapWOT.continuous_dual_apply ξ ψ) continuous_const

/-- **Supported strong-operator closure of a nonunital star subalgebra.** The strong operator
closure of `A` consists of those operators in `A''` that vanish on the common annihilator
`A.essentialSubspaceᗮ`. -/
theorem closure_image_toPointwiseConvergenceCLM (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  refine subset_antisymm
    (closure_minimal (Set.image_mono (subset_supported A))
      (ContinuousLinearMapWOT.isClosed_image_toPointwiseConvergenceCLM_of_isClosed_image_ofCLM
        (isClosed_image_ofCLM_supported A))) ?_
  rintro _ ⟨x, ⟨hx, hker⟩, rfl⟩
  rw [ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff_norm]
  intro F₀ ε hε
  obtain ⟨a, ha, happrox⟩ := A.exists_forall_norm_sub_apply_lt_of_mem_centralizer_centralizer
    hx hker (fun v : F₀ => (v : H)) hε
  exact ⟨a, ha, fun v hv => happrox ⟨v, hv⟩⟩

/-- **Supported weak-operator closure of a nonunital star subalgebra.** The weak operator closure
of `A` consists of those operators in `A''` that vanish on the common annihilator
`A.essentialSubspaceᗮ`. -/
theorem closure_image_ofCLM (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM ''
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} :=
  ContinuousLinearMapWOT.closure_image_ofCLM_eq_of_subset_closure_toPointwiseConvergenceCLM
    (subset_supported A) (isClosed_image_ofCLM_supported A)
    A.closure_image_toPointwiseConvergenceCLM.superset

/-- The strong operator closure of `A` on `H` is the zero extension from `A.essentialSubspace` of
the unital double commutant `(A.restrictEssentialSubspace)''`. -/
theorem closure_image_toPointwiseConvergenceCLM_eq_image_extendByZero
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A.essentialSubspace.extendByZero ''
          (A.restrictEssentialSubspace : Set _).centralizer.centralizer) := by
  rw [A.closure_image_toPointwiseConvergenceCLM, A.image_extendByZero_centralizer_centralizer]

/-- The weak operator closure of `A` on `H` is the zero extension from `A.essentialSubspace` of
the unital double commutant `(A.restrictEssentialSubspace)''`. -/
theorem closure_image_ofCLM_eq_image_extendByZero (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM ''
        (A.essentialSubspace.extendByZero ''
          (A.restrictEssentialSubspace : Set _).centralizer.centralizer) := by
  rw [A.closure_image_ofCLM, A.image_extendByZero_centralizer_centralizer]

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the strong operator closure of
`A`. -/
theorem toPointwiseConvergenceCLM_starProjection_essentialSubspace_mem_closure
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H
        A.essentialSubspace.starProjection ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H))) := by
  rw [A.closure_image_toPointwiseConvergenceCLM]
  exact ⟨A.essentialSubspace.starProjection,
    ⟨A.starProjection_essentialSubspace_mem_centralizer_centralizer, fun _ hξ =>
      A.essentialSubspace.starProjection_apply_eq_zero_iff.2 hξ⟩, rfl⟩

/-- The orthogonal projection onto `A.essentialSubspace` belongs to the weak operator closure of
`A`. -/
theorem ofCLM_starProjection_essentialSubspace_mem_closure
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMapWOT.ofCLM A.essentialSubspace.starProjection ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) := by
  rw [A.closure_image_ofCLM]
  exact ⟨A.essentialSubspace.starProjection,
    ⟨A.starProjection_essentialSubspace_mem_centralizer_centralizer, fun _ hξ =>
      A.essentialSubspace.starProjection_apply_eq_zero_iff.2 hξ⟩, rfl⟩

/-- For a nondegenerate nonunital star subalgebra (`A.essentialSubspace = ⊤`), its strong operator
closure is its unital double commutant `A''`. -/
theorem closure_image_toPointwiseConvergenceCLM_of_essentialSubspace_eq_top
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)} (hA : A.essentialSubspace = ⊤) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H)).centralizer.centralizer := by
  rw [A.closure_image_toPointwiseConvergenceCLM, hA, Submodule.top_orthogonal_eq_bot]
  congr 1
  ext x
  simp

/-- For a nondegenerate nonunital star subalgebra (`A.essentialSubspace = ⊤`), its weak operator
closure is its unital double commutant `A''`. -/
theorem closure_image_ofCLM_of_essentialSubspace_eq_top
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)} (hA : A.essentialSubspace = ⊤) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)).centralizer.centralizer := by
  rw [A.closure_image_ofCLM, hA, Submodule.top_orthogonal_eq_bot]
  congr 1
  ext x
  simp

/-- **Unitality on the essential subspace (strong operator topology).** The strong operator closure
of `A.restrictEssentialSubspace` on `A.essentialSubspace` is its unital double commutant
`(A.restrictEssentialSubspace)''`, which contains `1 : A.essentialSubspace →L[𝕜]
A.essentialSubspace`. -/
theorem closure_image_toPointwiseConvergenceCLM_restrictEssentialSubspace
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜)
      A.essentialSubspace A.essentialSubspace ''
      (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[𝕜] A.essentialSubspace))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜)
        A.essentialSubspace A.essentialSubspace ''
        (A.restrictEssentialSubspace :
          Set (A.essentialSubspace →L[𝕜] A.essentialSubspace)).centralizer.centralizer :=
  closure_image_toPointwiseConvergenceCLM_of_essentialSubspace_eq_top
    A.essentialSubspace_restrictEssentialSubspace

/-- **Unitality on the essential subspace (weak operator topology).** The weak operator closure of
`A.restrictEssentialSubspace` on `A.essentialSubspace` is its unital double commutant
`(A.restrictEssentialSubspace)''`, which contains `1 : A.essentialSubspace →L[𝕜]
A.essentialSubspace`. -/
theorem closure_image_ofCLM_restrictEssentialSubspace
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM ''
      (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[𝕜] A.essentialSubspace))) =
      ContinuousLinearMapWOT.ofCLM ''
        (A.restrictEssentialSubspace :
          Set (A.essentialSubspace →L[𝕜] A.essentialSubspace)).centralizer.centralizer :=
  closure_image_ofCLM_of_essentialSubspace_eq_top A.essentialSubspace_restrictEssentialSubspace

/-- The ambient identity operator `1 : H →L[𝕜] H` lies in the weak operator closure of `A` if and
only if `A.essentialSubspace = ⊤`. -/
theorem one_mem_closure_image_ofCLM_iff (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMapWOT.ofCLM (1 : H →L[𝕜] H) ∈
      closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) ↔
      A.essentialSubspace = ⊤ := by
  rw [A.closure_image_ofCLM, ContinuousLinearMapWOT.ofCLM_injective.mem_set_image, Set.mem_sep_iff]
  simp only [Set.one_mem_centralizer, true_and, one_apply_eq_self, ← Submodule.eq_bot_iff,
    Submodule.orthogonal_eq_bot_iff]

/-- The ambient identity operator `1 : H →L[𝕜] H` lies in the strong operator closure of `A` if and
only if `A.essentialSubspace = ⊤`. -/
theorem one_mem_closure_image_toPointwiseConvergenceCLM_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H (1 : H →L[𝕜] H) ∈
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H))) ↔
      A.essentialSubspace = ⊤ := by
  rw [A.closure_image_toPointwiseConvergenceCLM,
    ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image, Set.mem_sep_iff]
  simp only [Set.one_mem_centralizer, true_and, one_apply_eq_self, ← Submodule.eq_bot_iff,
    Submodule.orthogonal_eq_bot_iff]

/-- The weak operator closure of `A` equals the full double commutant `A''` on `H` if and only if
`A.essentialSubspace = ⊤`; otherwise `A''` strictly enlarges the closure by adjoining scalars on
the common annihilator. -/
theorem closure_image_ofCLM_eq_centralizer_centralizer_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      A.essentialSubspace = ⊤ := by
  refine ⟨fun h => A.one_mem_closure_image_ofCLM_iff.1 ?_,
    A.closure_image_ofCLM_of_essentialSubspace_eq_top⟩
  rw [h]
  exact ⟨1, Set.one_mem_centralizer, rfl⟩

/-- The strong operator closure of `A` equals the full double commutant `A''` on `H` if and only if
`A.essentialSubspace = ⊤`. -/
theorem closure_image_toPointwiseConvergenceCLM_eq_centralizer_centralizer_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H)).centralizer.centralizer ↔
      A.essentialSubspace = ⊤ := by
  refine ⟨fun h => A.one_mem_closure_image_toPointwiseConvergenceCLM_iff.1 ?_,
    A.closure_image_toPointwiseConvergenceCLM_of_essentialSubspace_eq_top⟩
  rw [h]
  exact ⟨1, Set.one_mem_centralizer, rfl⟩

/-- **Supported bicommutant criterion (weak operator topology).** A nonunital star subalgebra `A`
is weak operator closed if and only if it equals the set of operators in `A''` vanishing on
`A.essentialSubspaceᗮ`. -/
theorem isClosed_image_ofCLM_iff (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) ↔
      (A : Set (H →L[𝕜] H)) =
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  rw [← closure_eq_iff_isClosed, A.closure_image_ofCLM,
    (Set.image_injective.2 ContinuousLinearMapWOT.ofCLM_injective).eq_iff, eq_comm]

/-- **Supported bicommutant criterion (strong operator topology).** A nonunital star subalgebra `A`
is strong operator closed if and only if it equals the set of operators in `A''` vanishing on
`A.essentialSubspaceᗮ`. -/
theorem isClosed_image_toPointwiseConvergenceCLM_iff
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H))) ↔
      (A : Set (H →L[𝕜] H)) =
        {x ∈ (A : Set (H →L[𝕜] H)).centralizer.centralizer |
          ∀ ξ ∈ A.essentialSubspaceᗮ, x ξ = 0} := by
  rw [← closure_eq_iff_isClosed, A.closure_image_toPointwiseConvergenceCLM,
    (Set.image_injective.2 ContinuousLinearMap.toPointwiseConvergenceCLM_injective).eq_iff,
    eq_comm]

/-- A nonunital star subalgebra of bounded operators on `H` is weak operator closed if and only if
it is strong operator closed. -/
theorem isClosed_image_ofCLM_iff_isClosed_image_toPointwiseConvergenceCLM
    (A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)) :
    IsClosed (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H))) ↔
      IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
        (A : Set (H →L[𝕜] H))) :=
  A.isClosed_image_ofCLM_iff.trans A.isClosed_image_toPointwiseConvergenceCLM_iff.symm

/-- Any weak-operator closed nonunital star subalgebra contains the orthogonal projection onto its
essential subspace. -/
theorem starProjection_essentialSubspace_mem_of_isClosed_image_ofCLM
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}
    (hA : IsClosed (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[𝕜] H)))) :
    A.essentialSubspace.starProjection ∈ A := by
  have hmem := hA.closure_eq ▸ A.ofCLM_starProjection_essentialSubspace_mem_closure
  exact ContinuousLinearMapWOT.ofCLM_injective.mem_set_image.1 hmem

/-- Any strong-operator closed nonunital star subalgebra contains the orthogonal projection onto
its essential subspace. -/
theorem starProjection_essentialSubspace_mem_of_isClosed_image_toPointwiseConvergenceCLM
    {A : NonUnitalStarSubalgebra 𝕜 (H →L[𝕜] H)}
    (hA : IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (A : Set (H →L[𝕜] H)))) :
    A.essentialSubspace.starProjection ∈ A := by
  have hmem := hA.closure_eq ▸
    A.toPointwiseConvergenceCLM_starProjection_essentialSubspace_mem_closure
  exact ContinuousLinearMap.toPointwiseConvergenceCLM_injective.mem_set_image.1 hmem

end Closures

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **essential von Neumann algebra** of a nonunital star subalgebra `A` on a complex Hilbert
space `H`: the von Neumann algebra on `A.essentialSubspace` generated by
`A.restrictEssentialSubspace`, whose underlying operators are the strong and weak operator closures
of `A.restrictEssentialSubspace`. -/
def essentialVonNeumannAlgebra (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    VonNeumannAlgebra A.essentialSubspace :=
  VonNeumannAlgebra.adjoin
    (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))

/-- Unfolding formula for `NonUnitalStarSubalgebra.essentialVonNeumannAlgebra`. -/
theorem essentialVonNeumannAlgebra_def (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    A.essentialVonNeumannAlgebra =
      VonNeumannAlgebra.adjoin
        (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) :=
  (rfl)

/-- The underlying set of `A.essentialVonNeumannAlgebra` is `(A.restrictEssentialSubspace)''`. -/
@[simp]
theorem coe_essentialVonNeumannAlgebra (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (A.essentialVonNeumannAlgebra : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) =
      (A.restrictEssentialSubspace :
        Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)).centralizer.centralizer :=
  VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset

/-- `A.restrictEssentialSubspace` is contained in `A.essentialVonNeumannAlgebra`. -/
theorem subset_essentialVonNeumannAlgebra (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) ⊆
      A.essentialVonNeumannAlgebra :=
  VonNeumannAlgebra.subset_adjoin _

/-- `A.essentialVonNeumannAlgebra` is the smallest von Neumann algebra on `A.essentialSubspace`
containing `A.restrictEssentialSubspace`. -/
@[simp]
theorem essentialVonNeumannAlgebra_le_iff {A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    {M : VonNeumannAlgebra A.essentialSubspace} :
    A.essentialVonNeumannAlgebra ≤ M ↔
      (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) ⊆ M :=
  VonNeumannAlgebra.adjoin_le_iff

/-- The commutant of `A.essentialVonNeumannAlgebra` is `(A.restrictEssentialSubspace)'`. -/
theorem coe_commutant_essentialVonNeumannAlgebra (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (A.essentialVonNeumannAlgebra.commutant :
      Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) =
      (A.restrictEssentialSubspace :
        Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)).centralizer := by
  rw [essentialVonNeumannAlgebra_def, VonNeumannAlgebra.coe_commutant_adjoin,
    Set.union_eq_left.2 (StarMemClass.star_coe_eq A.restrictEssentialSubspace).subset]

/-- An operator on `A.essentialSubspace` belongs to `A.essentialVonNeumannAlgebra` if and only if
its extension by zero on `A.essentialSubspaceᗮ` belongs to `VonNeumannAlgebra.adjoin A`. -/
theorem mem_essentialVonNeumannAlgebra {A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    {S : A.essentialSubspace →L[ℂ] A.essentialSubspace} :
    S ∈ A.essentialVonNeumannAlgebra ↔
      A.essentialSubspace.extendByZero S ∈ VonNeumannAlgebra.adjoin (A : Set (H →L[ℂ] H)) := by
  rw [← SetLike.mem_coe, coe_essentialVonNeumannAlgebra, ← SetLike.mem_coe,
    VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset,
    A.extendByZero_mem_centralizer_centralizer_iff]

/-- `A.essentialVonNeumannAlgebra` is the weak operator closure of `A.restrictEssentialSubspace` on
`A.essentialSubspace`. -/
theorem image_ofCLM_essentialVonNeumannAlgebra_eq_closure
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    ContinuousLinearMapWOT.ofCLM ''
      (A.essentialVonNeumannAlgebra : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) =
      closure (ContinuousLinearMapWOT.ofCLM ''
        (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [coe_essentialVonNeumannAlgebra, A.closure_image_ofCLM_restrictEssentialSubspace]

/-- `A.essentialVonNeumannAlgebra` is the strong operator closure of `A.restrictEssentialSubspace`
on `A.essentialSubspace`. -/
theorem image_toPointwiseConvergenceCLM_essentialVonNeumannAlgebra_eq_closure
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        A.essentialSubspace A.essentialSubspace ''
      (A.essentialVonNeumannAlgebra : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace)) =
      closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
        A.essentialSubspace A.essentialSubspace ''
        (A.restrictEssentialSubspace : Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [coe_essentialVonNeumannAlgebra,
    A.closure_image_toPointwiseConvergenceCLM_restrictEssentialSubspace]

/-- On `H`, the weak operator closure of `A` is `A.essentialVonNeumannAlgebra` extended by zero on
the common annihilator `A.essentialSubspaceᗮ`. -/
theorem closure_image_ofCLM_eq_image_extendByZero_essentialVonNeumannAlgebra
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMapWOT.ofCLM '' (A : Set (H →L[ℂ] H))) =
      ContinuousLinearMapWOT.ofCLM ''
        (A.essentialSubspace.extendByZero ''
          (A.essentialVonNeumannAlgebra :
            Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [A.closure_image_ofCLM_eq_image_extendByZero, coe_essentialVonNeumannAlgebra]

/-- On `H`, the strong operator closure of `A` is `A.essentialVonNeumannAlgebra` extended by zero
on the common annihilator `A.essentialSubspaceᗮ`. -/
theorem closure_image_toPointwiseConvergenceCLM_eq_image_extendByZero_essentialVonNeumannAlgebra
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
      (A : Set (H →L[ℂ] H))) =
      ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
        (A.essentialSubspace.extendByZero ''
          (A.essentialVonNeumannAlgebra :
            Set (A.essentialSubspace →L[ℂ] A.essentialSubspace))) := by
  rw [A.closure_image_toPointwiseConvergenceCLM_eq_image_extendByZero,
    coe_essentialVonNeumannAlgebra]

/-- The unital von Neumann algebra `VonNeumannAlgebra.adjoin A` on `H` splits as the supported
closure `A.essentialSubspace.extendByZero '' A.essentialVonNeumannAlgebra` plus complex scalar
multiples of the identity on the common annihilator `A.essentialSubspaceᗮ`. -/
theorem coe_vonNeumannAlgebraAdjoin (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (VonNeumannAlgebra.adjoin (A : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) =
      {x | ∃ S ∈ A.essentialVonNeumannAlgebra, ∃ c : ℂ,
        x = A.essentialSubspace.extendByZero S + c • A.essentialSubspaceᗮ.starProjection} := by
  rw [VonNeumannAlgebra.coe_adjoin_of_star_subset (StarMemClass.star_coe_eq _).subset]
  ext x
  simp only [A.mem_centralizer_centralizer_iff, ← SetLike.mem_coe, coe_essentialVonNeumannAlgebra,
    Set.mem_ofPred]

end Complex

end NonUnitalStarSubalgebra

namespace Submodule

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- For any complete subspace `U` of `H`, the full supported algebra
`NonUnitalStarAlgHom.range U.extendByZero` is weak operator closed on `H`. -/
theorem isClosed_image_ofCLM_range_extendByZero (U : Submodule 𝕜 H) [CompleteSpace U] :
    IsClosed (ContinuousLinearMapWOT.ofCLM ''
      (NonUnitalStarAlgHom.range U.extendByZero : Set (H →L[𝕜] H))) := by
  let A := NonUnitalStarAlgHom.range U.extendByZero
  refine A.isClosed_image_ofCLM_iff.2
    (subset_antisymm (NonUnitalStarSubalgebra.subset_supported A) ?_)
  rw [← A.image_extendByZero_centralizer_centralizer, NonUnitalStarAlgHom.coe_range]
  rintro _ ⟨S, -, rfl⟩
  have hU := NonUnitalStarSubalgebra.essentialSubspace_range_extendByZero U
  exact U.mem_range_extendByZero_iff.2
    ⟨fun x => hU.le (A.essentialSubspace.extendByZero_apply_mem S x),
      fun x hx => A.essentialSubspace.extendByZero_apply_of_mem_orthogonal S
        (Submodule.orthogonal_le hU.le hx)⟩

/-- For any complete subspace `U` of `H`, the full supported algebra
`NonUnitalStarAlgHom.range U.extendByZero` is strong operator closed on `H`. -/
theorem isClosed_image_toPointwiseConvergenceCLM_range_extendByZero
    (U : Submodule 𝕜 H) [CompleteSpace U] :
    IsClosed (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) H H ''
      (NonUnitalStarAlgHom.range U.extendByZero : Set (H →L[𝕜] H))) :=
  (NonUnitalStarAlgHom.range
    U.extendByZero).isClosed_image_ofCLM_iff_isClosed_image_toPointwiseConvergenceCLM.1
    U.isClosed_image_ofCLM_range_extendByZero

end Submodule
