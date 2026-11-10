/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Splitting.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Coordinates for families of split kernels

If `A x` paired with a fixed coordinate `q` is invertible, then `q` identifies
`ker (A x)` with a fixed space `G`. These identifications are continuous on the
actual kernel locus in `X × E`, not just fibrewise. The inverse parametrization
is `ContinuousLinearMap.kerSection`; it has the regularity of the operator family.

This gives local product charts for kernels of surjective operator families. Between
finite-dimensional spaces, projections onto the range and the kernel of `A x₀` always give such
coordinates near `x₀` (`ContinuousLinearMap.exists_isOpen_isInvertible_prod_comp`), with an
inverse depending continuously on `x` for a continuous family
(`ContinuousLinearMap.exists_isOpen_continuousOn_inverse_prod_comp`).
For stabilized Fredholm operators the model `G` is finite dimensional, so these
charts are the local input for the determinant bundle construction. For a stabilizer `V` of the
target, the `V`-component of the normalized right inverse of `A x + inclusion_V` likewise has the
regularity of the family (`ContinuousLinearMap.contDiffAt_snd_comp_kerSection_coprod`); where `V`
is complementary to the range, it is the projection onto `V` along the range.

The construction uses Mathlib's smooth inversion of bounded operators and the
fixed-operator kernel section from `Splitting.Basic`.
-/

public section

open Set Topology
open scoped ContDiff

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The kernel section depends smoothly on the operator and the complementary coordinate
where their pair is invertible. -/
@[fun_prop]
theorem contDiffAt_kerSection {A : E →L[𝕜] F} {q : E →L[𝕜] G} {n : ℕ∞ω}
    (h : (A.prod q).IsInvertible) :
    ContDiffAt 𝕜 n (fun p : (E →L[𝕜] F) × (E →L[𝕜] G) ↦ p.1.kerSection p.2) (A, q) := by
  have hp : ContDiff 𝕜 n (fun p : (E →L[𝕜] F) × (E →L[𝕜] G) ↦ p.1.prod p.2) := by
    exact (prodL (𝕜 := 𝕜) (E := E) (F := F) (G := G) 𝕜).contDiff
  simp_rw [kerSection_def]
  exact (h.contDiffAt_map_inverse.comp (A, q) hp.contDiffAt).clm_comp
    (contDiffAt_const (c := inr 𝕜 F G))

section Stabilizer

variable {V : Submodule 𝕜 F} [CompleteSpace V] {q : (E × V) →L[𝕜] G}

/-- The stabilizer component of the normalized right inverse of `T x + inclusion_V` is continuous
at every parameter where the family is continuous and the pairing with `q` is invertible. -/
theorem continuousAt_snd_comp_kerSection_coprod {X : Type*} [TopologicalSpace X]
    {T : X → E →L[𝕜] F} {x : X} (hT : ContinuousAt T x)
    (hinv : (((T x).coprod V.subtypeL).prod q).IsInvertible) :
    ContinuousAt (fun y ↦ snd 𝕜 E V ∘L q.kerSection ((T y).coprod V.subtypeL)) x := by
  have hker := (contDiffAt_kerSection (n := 0) (isInvertible_prod_comm.mp hinv)).continuousAt
  exact continuousAt_const.clm_comp <| hker.comp
    (f := fun y ↦ (q, (T y).coprod V.subtypeL))
    (continuousAt_const.prodMk (hT.continuousLinearMapCoprod continuousAt_const))

/-- The stabilizer component of the normalized right inverse of `T x + inclusion_V` has the
regularity of the operator family, at every parameter where the pairing with `q` is invertible. -/
theorem contDiffAt_snd_comp_kerSection_coprod {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {T : X → E →L[𝕜] F} {x : X} {n : ℕ∞ω} (hT : ContDiffAt 𝕜 n T x)
    (hinv : (((T x).coprod V.subtypeL).prod q).IsInvertible) :
    ContDiffAt 𝕜 n (fun y ↦ snd 𝕜 E V ∘L q.kerSection ((T y).coprod V.subtypeL)) x := by
  have hcoprod : ContDiffAt 𝕜 n (fun y ↦ (T y).coprod V.subtypeL) x := by
    simp_rw [← comp_fst_add_comp_snd]
    exact (hT.clm_comp contDiffAt_const).add contDiffAt_const
  exact contDiffAt_const.clm_comp <|
    (contDiffAt_kerSection (isInvertible_prod_comm.mp hinv)).comp
      (f := fun y ↦ (q, (T y).coprod V.subtypeL)) x (contDiffAt_const.prodMk hcoprod)

end Stabilizer

variable {X : Type*} [TopologicalSpace X] {A : X → E →L[𝕜] F} {q : E →L[𝕜] G}

/-- Kernel sections are continuous on any continuous family of invertible pairs in which both
the operator and the complementary coordinate vary. -/
theorem _root_.Continuous.kerSection {A : X → E →L[𝕜] F} {q : X → E →L[𝕜] G}
    (hA : Continuous A) (hq : Continuous q) (h : ∀ x, ((A x).prod (q x)).IsInvertible) :
    Continuous (fun x ↦ (A x).kerSection (q x)) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  exact (contDiffAt_kerSection (n := 0) (h x)).continuousAt.comp
    (f := fun x ↦ (A x, q x)) (hA.continuousAt.prodMk hq.continuousAt)

/-- Kernel sections are continuous on any continuous family of invertible pairs with a fixed
complementary coordinate. -/
theorem continuous_kerSection (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible) :
    Continuous (fun x ↦ (A x).kerSection q) :=
  hA.kerSection continuous_const h

/-- Product coordinates on the actual kernel locus, with its subspace topology.
The base coordinate is unchanged, and the fibre coordinate is the fixed map `q`. -/
noncomputable def kernelHomeomorph (A : X → E →L[𝕜] F) (q : E →L[𝕜] G)
    (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible) :
    {p : X × E | A p.1 p.2 = 0} ≃ₜ X × G where
  toFun p := (p.val.1, q p.val.2)
  invFun p := ⟨(p.1, (A p.1).kerSection q p.2), apply_kerSection (h p.1) p.2⟩
  left_inv p := Subtype.ext (Prod.ext rfl (kerSection_apply_of_mem_ker (h p.val.1) p.property))
  right_inv p := Prod.ext rfl (apply_kerSection_right (h p.1) p.2)
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk
      (((continuous_kerSection hA h).comp continuous_fst).clm_apply continuous_snd)

@[simp]
theorem kernelHomeomorph_apply (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible)
    (p : {p : X × E | A p.1 p.2 = 0}) :
    kernelHomeomorph A q hA h p = (p.val.1, q p.val.2) :=
  (rfl)

@[simp]
theorem coe_kernelHomeomorph_symm_apply (hA : Continuous A)
    (h : ∀ x, ((A x).prod q).IsInvertible) (p : X × G) :
    ((kernelHomeomorph A q hA h).symm p).val = (p.1, (A p.1).kerSection q p.2) :=
  (rfl)

/-- On an overlap, changing the complementary coordinate acts by the bounded linear map
`q' ∘ kerSection (A x) q` on the fibre, with no change of base point. -/
theorem kernelHomeomorph_change_apply {G' : Type*}
    [NormedAddCommGroup G'] [NormedSpace 𝕜 G'] {q' : E →L[𝕜] G'}
    (hA : Continuous A) (h : ∀ x, ((A x).prod q).IsInvertible)
    (h' : ∀ x, ((A x).prod q').IsInvertible) (p : X × G) :
    kernelHomeomorph A q' hA h' ((kernelHomeomorph A q hA h).symm p) =
      (p.1, (q' ∘L (A p.1).kerSection q) p.2) :=
  (rfl)

/-- An invertible pair remains invertible on an open neighbourhood for a family continuous
at the base point. The same complementary coordinate gives kernel coordinates throughout
that neighbourhood. -/
theorem exists_isOpen_isInvertible_prod {x₀ : X} (hA : ContinuousAt A x₀)
    (h : ((A x₀).prod q).IsInvertible) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, ((A x).prod q).IsInvertible := by
  have hp : ContinuousAt (fun x ↦ (A x).prod q) x₀ :=
    (prodL (𝕜 := 𝕜) (E := E) (F := F) (G := G) 𝕜).continuousAt.comp
      (hA.prodMk continuousAt_const)
  obtain ⟨U, hUsub, hU, hx₀⟩ := mem_nhds_iff.mp (hp.eventually h.eventually_nhds)
  exact ⟨U, hU, hx₀, fun _ hx ↦ hUsub hx⟩

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [TopologicalSpace X] {A : X → E →L[𝕜] F}

/-- Splitting coordinates for a family of operators between finite-dimensional spaces: a
continuous projection `p` onto `range (A x₀)` and a continuous projection `q` onto
`ker (A x₀)` such that the pair `(p ∘ A x, q)` is invertible on an open neighbourhood of `x₀`. -/
theorem exists_isOpen_isInvertible_prod_comp {x₀ : X} (hA : ContinuousAt A x₀) :
    ∃ p : F →L[𝕜] (A x₀).range, (∀ y : (A x₀).range, p y = y) ∧
      ∃ q : E →L[𝕜] (A x₀).ker, (∀ v : (A x₀).ker, q v = v) ∧
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, ((p ∘L A x).prod q).IsInvertible := by
  have := FiniteDimensional.complete 𝕜 E
  obtain ⟨p, hp⟩ := Submodule.ClosedComplemented.of_finiteDimensional_quotient
    (Submodule.closed_of_finiteDimensional (A x₀).range)
  obtain ⟨q, hq⟩ := (A x₀).ker_closedComplemented_of_finiteDimensional_range
  -- At `x₀` the pair is injective between spaces of equal dimension, hence invertible.
  have hinj := prod_comp_injective hp hq
  have hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 ((A x₀).range × (A x₀).ker) := by
    rw [Module.finrank_prod, LinearMap.finrank_range_add_finrank_ker]
  let e : E ≃L[𝕜] (A x₀).range × (A x₀).ker :=
    (LinearEquiv.ofBijective ((p ∘L A x₀).prod q : E →ₗ[𝕜] _)
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
      ).toContinuousLinearEquiv
  have he : (e : E →L[𝕜] (A x₀).range × (A x₀).ker) = (p ∘L A x₀).prod q :=
    ContinuousLinearMap.ext fun v ↦ by
      simp [e, LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.ofBijective_apply]
  exact ⟨p, hp, q, hq, exists_isOpen_isInvertible_prod (continuousAt_const.clm_comp hA) ⟨e, he⟩⟩

/-- Splitting coordinates for a continuous family of operators between finite-dimensional
spaces, with a continuous inverse: a continuous projection `p` onto `range (A x₀)` and a
continuous projection `q` onto `ker (A x₀)` such that, on an open neighbourhood `U ⊆ s` of `x₀`,
the pair `(p ∘ A x, q)` is invertible and its inverse depends continuously on `x`. -/
theorem exists_isOpen_continuousOn_inverse_prod_comp {s : Set X} {x₀ : X}
    (hA : ContinuousOn A s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ p : F →L[𝕜] (A x₀).range, (∀ y : (A x₀).range, p y = y) ∧
      ∃ q : E →L[𝕜] (A x₀).ker, (∀ v : (A x₀).ker, q v = v) ∧
        ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ (∀ x ∈ U, ((p ∘L A x).prod q).IsInvertible) ∧
          ContinuousOn (fun x ↦ ((p ∘L A x).prod q).inverse) U := by
  have := FiniteDimensional.complete 𝕜 E
  obtain ⟨p, hp, q, hq, V, hV, hx₀V, hinv⟩ :=
    exists_isOpen_isInvertible_prod_comp (hA.continuousAt (hs.mem_nhds hx₀))
  have hT : ContinuousOn (fun x ↦ (p ∘L A x).prod q) s :=
    (prodL 𝕜).continuous.comp_continuousOn
      ((continuousOn_const.clm_comp hA).prodMk continuousOn_const)
  refine ⟨p, hp, q, hq, s ∩ V, inter_subset_left, hs.inter hV, ⟨hx₀, hx₀V⟩,
    fun x hx ↦ hinv x hx.2, fun x hx ↦ ?_⟩
  exact ((hinv x hx.2).contDiffAt_map_inverse (n := 0)).continuousAt.comp_continuousWithinAt
    (f := fun x ↦ (p ∘L A x).prod q) ((hT x hx.1).mono inter_subset_left)

end ContinuousLinearMap
