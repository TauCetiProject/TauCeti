/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Open
public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.Analysis.Fredholm.Stabilization
public import TauCeti.Topology.VectorBundle.Subbundle

/-!
# Fredholm families of constant nullity

Let `T x : E →L[𝕜] F` be a family of operators between Banach spaces, continuous at a point `x₀`
where `T x₀` is Fredholm. The dimensions of the kernel and of the cokernel of `T x` can only drop
near `x₀` (`ContinuousLinearMap.IsFredholm.eventually_finrank_ker_le` and
`ContinuousLinearMap.IsFredholm.eventually_finrank_quotient_range_le`), and since the index is
locally constant they drop together: near `x₀` the nullity of `T x` is that of `T x₀` exactly
when its conullity is (`ContinuousLinearMap.IsFredholm.eventually_finrank_ker_eq_iff`).

This file shows that the parameters near `x₀` where the nullity does not drop are those where a
single finite-dimensional complement `S` of the range of `T x₀` stays a complement of the range
of `T x`, and that there the kernels and the cokernels of `T x` move continuously:

* `ContinuousLinearMap.IsFredholm.exists_stabilization_isTopCompl_range_iff`: the stabilizer `S`
  of `ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates` is a topological
  complement of the range of `T x` exactly where the nullity of `T x` is that of `T x₀`. There
  the kernel of the stabilized operator `T x + inclusion_S` is `ker (T x) × 0`
  (`ContinuousLinearMap.ker_coprod_of_disjoint_range`).
* `ContinuousLinearMap.IsFredholm.exists_continuousOn_ker_parametrization`: a continuous family of
  operators `κ x : ker (T x₀) →L[𝕜] E` which, where the nullity is that of `T x₀`, is injective with
  range `ker (T x)`. For a `C^n` family it is `C^n`
  (`ContinuousLinearMap.IsFredholm.exists_contDiffOn_ker_parametrization`).
* `ContinuousLinearMap.IsFredholm.exists_continuousOn_splitting`: continuous families of
  operators `R x : F →L[𝕜] E` and `P x : F →L[𝕜] S` with `T x ∘ R x + P x = id`, where `P x` is the
  projection onto `S` along the range of `T x` wherever the nullity is that of `T x₀`. So `R x` is a
  right inverse of `T x` on its range, bounded uniformly on compact subsets of the neighbourhood
  of `x₀` given by the theorem, and `P x` identifies the cokernel of `T x` with `S`. For a `C^n`
  family both are `C^n`
  (`ContinuousLinearMap.IsFredholm.exists_contDiffOn_splitting`).
* `TauCeti.hasLocalSubbundleFrames_ker_of_isFredholm`: on a set of parameters where the operators
  are Fredholm of a fixed nullity, the kernels have continuous local frames, so over `ℝ` or `ℂ`
  they form a vector bundle, a subbundle of the trivial bundle with fibre `E`.

The proofs read everything off the stabilized operator `T x + inclusion_S`. It is surjective near
`x₀`, so `F = range (T x) + S` and the conullity of `T x` is at most `dim S`, which is the conullity
of `T x₀`. When the two conullities agree, `S` meets the range of `T x` trivially, so a vector
`(e, s)` of the stabilized kernel has `s = 0`; the stabilized kernels, which move continuously
(`ContinuousLinearMap.kerSection`), are then the kernels of `T x`. Across a drop of the nullity
only the stabilized kernels form a bundle
(`ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_vectorBundle`); the kernels of `T x`
themselves do not.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix A.2 (stabilization of Fredholm families and their kernel bundles).
* T. Kato, *Perturbation Theory for Linear Operators*, second edition, Chapter IV, §5.1
  (semicontinuity of the nullity and deficiency of semi-Fredholm operators).
-/

public section

open Function Module Set Topology Filter
open scoped ContDiff

namespace ContinuousLinearMap

section Family

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace X] {T : X → E →L[𝕜] F} {x₀ : X}

/-- The stabilizer of `ContinuousLinearMap.IsFredholm.exists_stabilization_kernel_coordinates`,
with every operator near `x₀` Fredholm of the index of `T x₀`. -/
private theorem IsFredholm.exists_stabilization_index_eq (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) {D : Submodule 𝕜 F} (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ S.IsTopCompl (T x₀).range ∧ FiniteDimensional 𝕜 S ∧
      ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U,
          (((T x).coprod S.subtypeL).prod q).IsInvertible ∧ IsFredholm (T x) ∧
            (T x : E →ₗ[𝕜] F).index = (T x₀ : E →ₗ[𝕜] F).index := by
  obtain ⟨S, hSD, hS, hSfin, q, U, hU, hx₀, hinv⟩ :=
    hT₀.exists_stabilization_kernel_coordinates hT hD
  have hev : ∀ᶠ x in 𝓝 x₀,
      IsFredholm (T x) ∧ (T x : E →ₗ[𝕜] F).index = (T x₀ : E →ₗ[𝕜] F).index :=
    (hT.eventually hT₀.eventually_nhds).and (hT.eventually hT₀.eventually_nhds_index_eq)
  obtain ⟨V, hVsub, hV, hx₀V⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx₀) hev)
  exact ⟨S, hSD, hS, hSfin, q, V, hV, hx₀V, fun x hx ↦ ⟨hinv x (hVsub hx).1, (hVsub hx).2⟩⟩

/-- **Upper semicontinuity of the conullity.** Near a parameter where a family continuous there
is Fredholm, the cokernel can only shrink. -/
theorem IsFredholm.eventually_finrank_quotient_range_le (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) :
    ∀ᶠ x in 𝓝 x₀, finrank 𝕜 (F ⧸ (T x).range) ≤ finrank 𝕜 (F ⧸ (T x₀).range) := by
  obtain ⟨S, -, hS, hSfin, q, U, hU, hx₀, hU'⟩ :=
    hT₀.exists_stabilization_index_eq hT (D := ⊤) (by simp)
  filter_upwards [hU.mem_nhds hx₀] with x hx
  obtain ⟨hinv, hfred, -⟩ := hU' x hx
  have := hfred.finite_coker
  -- `T x + inclusion_S` is surjective, so `S` maps onto the cokernel of `T x`.
  have h := finrank_quotient_range_coprod_add_finrank_range_parameterToCoker (T x) S.subtypeL
  rw [LinearMap.range_eq_top.mpr (surjective_of_isInvertible_prod hinv),
    finrank_eq_zero_of_rank_eq_zero (by simp), zero_add] at h
  rw [← h, ((T x₀).range.quotientEquivOfIsCompl S hS.isCompl.symm).finrank_eq]
  exact LinearMap.finrank_range_le _

/-- **Upper semicontinuity of the nullity.** Near a parameter where a family continuous there is
Fredholm, the kernel can only shrink. -/
theorem IsFredholm.eventually_finrank_ker_le (hT₀ : IsFredholm (T x₀)) (hT : ContinuousAt T x₀) :
    ∀ᶠ x in 𝓝 x₀, finrank 𝕜 (T x).ker ≤ finrank 𝕜 (T x₀).ker := by
  filter_upwards [hT₀.eventually_finrank_quotient_range_le hT,
    hT.eventually hT₀.eventually_nhds_index_eq] with x hcoker hindex
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub] at hindex
  omega

omit [CompleteSpace F] in
/-- Near a parameter where a family continuous there is Fredholm, the kernel keeps its dimension
exactly where the cokernel does, since the index is locally constant. -/
theorem IsFredholm.eventually_finrank_ker_eq_iff (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) :
    ∀ᶠ x in 𝓝 x₀, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker ↔
      finrank 𝕜 (F ⧸ (T x).range) = finrank 𝕜 (F ⧸ (T x₀).range) := by
  filter_upwards [hT.eventually hT₀.eventually_nhds_index_eq] with x hindex
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub] at hindex
  omega

/-- **The exact stabilizer of a family of constant nullity.** A family continuous at `x₀`, where
it is Fredholm, has a finite-dimensional stabilizer `S`, inside any prescribed dense subspace `D`
of the target, and a fixed kernel coordinate `q`, such that on an open neighbourhood `U` of `x₀`
the stabilized operators `T x + inclusion_S` paired with `q` are invertible, the operators `T x`
are Fredholm, and `S` is a topological complement of the range of `T x` exactly where the kernel
of `T x` has the dimension of that of `T x₀`. There the kernel of `T x + inclusion_S` is
`ker (T x) × 0` (`ContinuousLinearMap.ker_coprod_of_disjoint_range`). -/
theorem IsFredholm.exists_stabilization_isTopCompl_range_iff (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) {D : Submodule 𝕜 F} (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ FiniteDimensional 𝕜 S ∧
      ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U,
          (((T x).coprod S.subtypeL).prod q).IsInvertible ∧ IsFredholm (T x) ∧
            (S.IsTopCompl (T x).range ↔ finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker) := by
  obtain ⟨S, hSD, hS, hSfin, q, U, hU, hx₀, hU'⟩ := hT₀.exists_stabilization_index_eq hT hD
  refine ⟨S, hSD, hSfin, q, U, hU, hx₀, fun x hx ↦ ⟨(hU' x hx).1, (hU' x hx).2.1, ?_⟩⟩
  obtain ⟨hinv, -, hindex⟩ := hU' x hx
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub] at hindex
  have hS₀ := ((T x₀).range.quotientEquivOfIsCompl S hS.isCompl.symm).finrank_eq
  constructor
  · intro hSx
    have := ((T x).range.quotientEquivOfIsCompl S hSx.isCompl.symm).finrank_eq
    omega
  · intro hker
    exact isTopCompl_of_isInvertible_prod_coprod hinv (by omega)

omit [CompleteSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The kernel parametrization at a single parameter: if `S` meets the ranges of both `T₀` and
`T` trivially, the `E`-component of the kernel section of `T + inclusion_S`, precomposed with
`ContinuousLinearMap.kerCoprodHom`, is injective with range `ker T`. The `T`-side is
`ContinuousLinearMap.injective_fst_comp_kerSection_coprod` and
`ContinuousLinearMap.range_fst_comp_kerSection_coprod`; at `T₀` the embedding `kerCoprodHom` is
onto the stabilized kernel `ker T₀ × 0`. -/
private theorem injective_and_range_fst_comp_kerSection {S : Submodule 𝕜 F} {T₀ T : E →L[𝕜] F}
    {q : (E × S) →L[𝕜] (T₀.coprod S.subtypeL).ker}
    (hinv : ((T.coprod S.subtypeL).prod q).IsInvertible) (hS₀ : Disjoint S T₀.range)
    (hS : Disjoint S T.range) :
    Injective (fst 𝕜 E S ∘L (T.coprod S.subtypeL).kerSection q ∘L kerCoprodHom T₀ S.subtypeL) ∧
      (fst 𝕜 E S ∘L (T.coprod S.subtypeL).kerSection q ∘L kerCoprodHom T₀ S.subtypeL).range =
        T.ker := by
  have hker₀ : (T₀.coprod S.subtypeL).ker = T₀.ker.prod ⊥ := by
    simpa using ker_coprod_of_disjoint_range (f₂ := S.subtypeL) (by simpa [disjoint_comm] using hS₀)
  have hk : Surjective (kerCoprodHom T₀ S.subtypeL) := fun g ↦ by
    have hg := (hker₀ ▸ g.2 : (g : E × S) ∈ T₀.ker.prod ⊥)
    exact ⟨⟨(g : E × S).1, hg.1⟩, Subtype.ext <| (kerCoprodHom_apply _ _ _).trans
      (Prod.ext rfl (Submodule.mem_bot 𝕜 |>.mp hg.2).symm)⟩
  refine ⟨(injective_fst_comp_kerSection_coprod hinv hS).comp (kerCoprodHom_injective _ _), ?_⟩
  rw [← range_fst_comp_kerSection_coprod hinv hS]
  rw [← comp_assoc]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hk)

/-- The kernel parametrization of a family of constant nullity, as an explicit formula: on a
neighbourhood `U` of `x₀`, `κ x` is the `E`-component of the stabilized kernel section, and it is
injective with range `ker (T x)` wherever the nullity of `T x` is that of `T x₀`. -/
private theorem IsFredholm.exists_ker_parametrization (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousAt T x₀) :
    ∃ S : Submodule 𝕜 F, FiniteDimensional 𝕜 S ∧
      ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U,
          (((T x).coprod S.subtypeL).prod q).IsInvertible ∧
            (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
              Injective (fst 𝕜 E S ∘L ((T x).coprod S.subtypeL).kerSection q ∘L
                kerCoprodHom (T x₀) S.subtypeL) ∧
              (fst 𝕜 E S ∘L ((T x).coprod S.subtypeL).kerSection q ∘L
                kerCoprodHom (T x₀) S.subtypeL).range = (T x).ker) := by
  obtain ⟨S, -, hSfin, q, U, hU, hx₀, hU'⟩ :=
    hT₀.exists_stabilization_isTopCompl_range_iff hT (D := ⊤) (by simp)
  have hS₀ := ((hU' x₀ hx₀).2.2.mpr rfl).isCompl.disjoint
  exact ⟨S, hSfin, q, U, hU, hx₀, fun x hx ↦ ⟨(hU' x hx).1, fun hker ↦
    injective_and_range_fst_comp_kerSection (hU' x hx).1 hS₀
      ((hU' x hx).2.2.mpr hker).isCompl.disjoint⟩⟩

/-- **Kernels of a Fredholm family of constant nullity move continuously.** If `T` is continuous
on an open set `s` and Fredholm at `x₀ ∈ s`, then near `x₀` there is a family of operators
`κ x : ker (T x₀) →L[𝕜] E`, continuous in `x`, which is injective with range `ker (T x)` at every
parameter where the kernel of `T x` has the dimension of that of `T x₀`. No assumption is made on
the other parameters, where the kernel is smaller. -/
theorem IsFredholm.exists_continuousOn_ker_parametrization {s : Set X} (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousOn T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ κ : X → (T x₀).ker →L[𝕜] E, ContinuousOn κ U ∧
      ∀ x ∈ U, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        Injective (κ x) ∧ (κ x).range = (T x).ker := by
  obtain ⟨S, hSfin, q, U, hU, hx₀U, hU'⟩ :=
    hT₀.exists_ker_parametrization (hT.continuousAt (hs.mem_nhds hx₀))
  have : CompleteSpace S := FiniteDimensional.completeSpace 𝕜 S
  refine ⟨U ∩ s, inter_subset_right, hU.inter hs, ⟨hx₀U, hx₀⟩, _, fun x hx ↦ ?_,
    fun x hx ↦ (hU' x hx.1).2⟩
  have hsec : ContinuousAt (fun y ↦ ((T y).coprod S.subtypeL).kerSection q) x :=
    ((hT.continuousAt (hs.mem_nhds hx.2)).continuousLinearMapCoprod
      continuousAt_const).kerSection continuousAt_const (hU' x hx.1).1
  exact (continuousAt_const.clm_comp (hsec.clm_comp continuousAt_const)).continuousWithinAt

/-- **Kernels of a `C^n` Fredholm family of constant nullity move `C^n`.** The parametrization of
`ContinuousLinearMap.IsFredholm.exists_continuousOn_ker_parametrization` has the regularity of the
family. -/
theorem IsFredholm.exists_contDiffOn_ker_parametrization {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {T : X → E →L[𝕜] F} {x₀ : X} {s : Set X} {n : ℕ∞ω}
    (hT₀ : IsFredholm (T x₀)) (hT : ContDiffOn 𝕜 n T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) :
    ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧ ∃ κ : X → (T x₀).ker →L[𝕜] E, ContDiffOn 𝕜 n κ U ∧
      ∀ x ∈ U, finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
        Injective (κ x) ∧ (κ x).range = (T x).ker := by
  obtain ⟨S, hSfin, q, U, hU, hx₀U, hU'⟩ := hT₀.exists_ker_parametrization
    (hT.continuousOn.continuousAt (hs.mem_nhds hx₀))
  have : CompleteSpace S := FiniteDimensional.completeSpace 𝕜 S
  refine ⟨U ∩ s, inter_subset_right, hU.inter hs, ⟨hx₀U, hx₀⟩, _, fun x hx ↦ ?_,
    fun x hx ↦ (hU' x hx.1).2⟩
  have hsec : ContDiffAt 𝕜 n (fun y ↦ ((T y).coprod S.subtypeL).kerSection q) x :=
    ((hT.contDiffAt (hs.mem_nhds hx.2)).continuousLinearMapCoprod
      contDiffAt_const).kerSection contDiffAt_const (hU' x hx.1).1
  exact (contDiffAt_const.clm_comp (hsec.clm_comp contDiffAt_const)).contDiffWithinAt

/-- The splitting of a family of constant nullity, as an explicit formula: on a neighbourhood
`U` of `x₀`, the components of the right inverse of `T x + inclusion_S` normalized by `q = 0`
split each vector of `F` into a value of `T x` and a vector of `S`, and the `S`-component is the
projection onto `S` along the range of `T x` wherever the nullity of `T x` is that of `T x₀`. -/
private theorem IsFredholm.exists_splitting (hT₀ : IsFredholm (T x₀)) (hT : ContinuousAt T x₀)
    {D : Submodule 𝕜 F} (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ FiniteDimensional 𝕜 S ∧
      ∃ q : (E × S) →L[𝕜] ((T x₀).coprod S.subtypeL).ker,
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U,
          (((T x).coprod S.subtypeL).prod q).IsInvertible ∧
            (∀ y, T x ((fst 𝕜 E S ∘L q.kerSection ((T x).coprod S.subtypeL)) y) +
              (snd 𝕜 E S ∘L q.kerSection ((T x).coprod S.subtypeL)) y = y) ∧
            (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
              ∃ hS : S.IsTopCompl (T x).range,
                snd 𝕜 E S ∘L q.kerSection ((T x).coprod S.subtypeL) =
                  S.projectionOntoL (T x).range hS) := by
  obtain ⟨S, hSD, hSfin, q, U, hU, hx₀U, hU'⟩ :=
    hT₀.exists_stabilization_isTopCompl_range_iff hT hD
  refine ⟨S, hSD, hSfin, q, U, hU, hx₀U, fun x hx ↦ ⟨(hU' x hx).1,
    fun y ↦ by simpa using apply_fst_kerSection_coprod_add_snd (hU' x hx).1 y, fun hker ↦ ?_⟩⟩
  have hS := (hU' x hx).2.2.mpr hker
  exact ⟨hS, (projectionOntoL_eq_snd_comp_kerSection_coprod (hU' x hx).1 hS).symm⟩

/-- **Splittings and right inverses of a Fredholm family of constant nullity.** If `T` is
continuous on an open set `s` and Fredholm at `x₀ ∈ s`, there are a finite-dimensional subspace `S`
of the target, inside any prescribed dense subspace `D`, and families of operators
`R x : F →L[𝕜] E` and `P x : F →L[𝕜] S`, continuous near `x₀`, with `T x (R x y) + P x y = y`.
Wherever the kernel of `T x` has the dimension of that of `T x₀`, `S` is a topological complement
of the range of `T x` and `P x` is the projection onto `S` along that range, so that `P x`
identifies the cokernel of `T x` with `S` and `R x` is a right inverse of `T x` on its range. Being
continuous, the right inverses are bounded uniformly on compact subsets of `U`
(`IsCompact.exists_bound_of_continuousOn`). -/
theorem IsFredholm.exists_continuousOn_splitting {s : Set X} (hT₀ : IsFredholm (T x₀))
    (hT : ContinuousOn T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s) {D : Submodule 𝕜 F}
    (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ FiniteDimensional 𝕜 S ∧ ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧
      ∃ R : X → F →L[𝕜] E, ∃ P : X → F →L[𝕜] S, ContinuousOn R U ∧ ContinuousOn P U ∧
        ∀ x ∈ U, (∀ y, T x (R x y) + P x y = y) ∧
          (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
            ∃ hS : S.IsTopCompl (T x).range, P x = S.projectionOntoL (T x).range hS) := by
  obtain ⟨S, hSD, hSfin, q, U, hU, hx₀U, hU'⟩ :=
    hT₀.exists_splitting (hT.continuousAt (hs.mem_nhds hx₀)) hD
  have : CompleteSpace S := FiniteDimensional.completeSpace 𝕜 S
  have hsec {x} (hx : x ∈ U ∩ s) :=
    continuousAt_kerSection_coprod (hT.continuousAt (hs.mem_nhds hx.2)) (hU' x hx.1).1
  exact ⟨S, hSD, hSfin, U ∩ s, inter_subset_right, hU.inter hs, ⟨hx₀U, hx₀⟩, _, _,
    fun x hx ↦ (continuousAt_const.clm_comp (hsec hx)).continuousWithinAt,
    fun x hx ↦ (continuousAt_const.clm_comp (hsec hx)).continuousWithinAt,
    fun x hx ↦ (hU' x hx.1).2⟩

/-- **Splittings of a `C^n` Fredholm family of constant nullity are `C^n`.** The right inverses and
cokernel projections of `ContinuousLinearMap.IsFredholm.exists_continuousOn_splitting` have the
regularity of the family. -/
theorem IsFredholm.exists_contDiffOn_splitting {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {T : X → E →L[𝕜] F} {x₀ : X} {s : Set X} {n : ℕ∞ω}
    (hT₀ : IsFredholm (T x₀)) (hT : ContDiffOn 𝕜 n T s) (hs : IsOpen s) (hx₀ : x₀ ∈ s)
    {D : Submodule 𝕜 F} (hD : Dense (D : Set F)) :
    ∃ S : Submodule 𝕜 F, S ≤ D ∧ FiniteDimensional 𝕜 S ∧ ∃ U ⊆ s, IsOpen U ∧ x₀ ∈ U ∧
      ∃ R : X → F →L[𝕜] E, ∃ P : X → F →L[𝕜] S, ContDiffOn 𝕜 n R U ∧ ContDiffOn 𝕜 n P U ∧
        ∀ x ∈ U, (∀ y, T x (R x y) + P x y = y) ∧
          (finrank 𝕜 (T x).ker = finrank 𝕜 (T x₀).ker →
            ∃ hS : S.IsTopCompl (T x).range, P x = S.projectionOntoL (T x).range hS) := by
  obtain ⟨S, hSD, hSfin, q, U, hU, hx₀U, hU'⟩ :=
    hT₀.exists_splitting (hT.continuousOn.continuousAt (hs.mem_nhds hx₀)) hD
  have : CompleteSpace S := FiniteDimensional.completeSpace 𝕜 S
  have hsec {x} (hx : x ∈ U ∩ s) :=
    contDiffAt_kerSection_coprod (hT.contDiffAt (hs.mem_nhds hx.2)) (hU' x hx.1).1
  exact ⟨S, hSD, hSfin, U ∩ s, inter_subset_right, hU.inter hs, ⟨hx₀U, hx₀⟩, _, _,
    fun x hx ↦ (contDiffAt_const.clm_comp (hsec hx)).contDiffWithinAt,
    fun x hx ↦ (contDiffAt_const.clm_comp (hsec hx)).contDiffWithinAt,
    fun x hx ↦ (hU' x hx.1).2⟩

end Family


end ContinuousLinearMap

namespace TauCeti

open Bundle ContinuousLinearMap

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace X] {T : X → E →L[𝕜] F}

/-- **Kernels of a Fredholm family of constant nullity have local frames.** If `T` is continuous
on an open set `W`, and Fredholm with kernels of dimension `r` at every point of a set `s ⊆ W`,
then the kernels `ker (T x)`, `x ∈ s`, have continuous local frames with `r` members near every
point of `s`, as subspaces of the fibres of the trivial bundle `s × E`. Over `ℝ` or `ℂ` they
therefore form a vector bundle, with the topology of a subspace of `s × E`
(`TauCeti.HasLocalSubbundleFrames.vectorBundle`). -/
theorem hasLocalSubbundleFrames_ker_of_isFredholm {W s : Set X} (hT : ContinuousOn T W)
    (hW : IsOpen W) (hsW : s ⊆ W) {r : ℕ} (hfred : ∀ x ∈ s, IsFredholm (T x))
    (hr : ∀ x ∈ s, finrank 𝕜 (T x).ker = r) :
    HasLocalSubbundleFrames E (Fin r) (E := Trivial s E) fun x : s ↦ (T x).ker := by
  refine hasLocalSubbundleFrames_iff.mpr fun x₀ ↦ ?_
  have := (hfred x₀ x₀.2).finite_ker
  obtain ⟨U, -, hU, hx₀U, κ, hκ, hκU⟩ :=
    (hfred x₀ x₀.2).exists_continuousOn_ker_parametrization hT hW (hsW x₀.2)
  have hκU' (x : s) (hx : (x : X) ∈ U) := hκU x hx (by rw [hr x x.2, hr x₀ x₀.2])
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hx₀U, _,
    Trivialization.isSubbundleFrameOn_symm_comp (Trivial.trivialization s E) (subset_univ _)
      (hκ.comp continuous_subtype_val.continuousOn (mapsTo_preimage _ _))
      (finBasisOfFinrankEq 𝕜 _ (hr x₀ x₀.2)) (fun x hx ↦ (hκU' x hx).1) fun x hx v ↦ ?_⟩
  rw [Function.comp_apply, (hκU' x hx).2, Trivial.trivialization_symm_apply]

end TauCeti
