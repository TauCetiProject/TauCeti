/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Symplectic.Liouville.LinearAtInfinity
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Exact codimension-zero embeddings of Liouville domains

Let `(W, α)` and `(W', α')` be Liouville domains. An **exact codimension-zero embedding** of `W`
into `W'` is a smooth embedding `φ` of `W` into the interior of `W'`, between manifolds of the
same dimension, that pulls the Liouville primitive back to the Liouville primitive up to an exact
form: `φ^* α' = α + dh` for a smooth function `h`, the **primitive** of `φ`. It then pulls
`ω' = dα'` back to `ω = dα`, so it is a codimension-zero symplectic embedding. These are the maps
along which symplectic homology has Viterbo's transfer maps `SH(W') → SH(W)`.

Liouville domains are realized as compact subsets of ambient manifolds
(`TauCeti.IsLiouvilleDomain`), and so are these embeddings
(`TauCeti.IsExactLiouvilleEmbedding`): `φ : M → M'` is a smooth map of the ambient manifolds, a
local diffeomorphism at every point of `W`, injective on `W`, and carrying `W` into the interior of
`W'`, and `φ^* α' = α + dh` holds on a neighbourhood of `W`. Apart from the smoothness of `φ`,
required on the whole ambient manifold, these conditions only involve `φ` near `W`. By compactness
of `W`, the map `φ` is then an injective local diffeomorphism on an open neighbourhood of `W`
(`TauCeti.IsExactLiouvilleEmbedding.exists_isOpen_injOn`), that is, a diffeomorphism of that
neighbourhood onto an open subset of `M'`. As for exact Lagrangian maps, the primitive `h` is part
of the data: it measures how the embedding shifts actions of periodic orbits.

Exact codimension-zero embeddings compose, with primitives adding along the composition
(`TauCeti.IsExactLiouvilleEmbedding.comp`), and a Liouville domain lying in the interior of
another one for the same primitive embeds into it by the identity
(`TauCeti.isExactLiouvilleEmbedding_id`). For instance, a Liouville domain `W` embeds in this way
into each truncation `{r ≤ c}`, `c > 1`, of its completion: `W` lies in its interior
(`TauCeti.IsLiouvilleCompletion.subset_interior_setOf_liouvilleRadialCoordinate_le`), and it is
again a Liouville domain
(`TauCeti.IsLiouvilleCompletion.isLiouvilleDomain_setOf_liouvilleRadialCoordinate_le`).

## Main definitions

* `TauCeti.IsExactLiouvilleEmbedding`: exact codimension-zero embeddings, with a specified
  primitive.

## Main results

* `TauCeti.IsExactLiouvilleEmbedding.eventually_mpullback_mextDeriv_eq`: an exact
  codimension-zero embedding pulls `dα'` back to `dα` near `W`.
* `TauCeti.IsExactLiouvilleEmbedding.exists_isOpen_injOn`: it is an injective local
  diffeomorphism on an open neighbourhood of `W`.
* `TauCeti.isExactLiouvilleEmbedding_id`, `TauCeti.IsExactLiouvilleEmbedding.comp`: identities
  and composites.

## References

* C. Viterbo, *Functors and computations in Floer homology with applications. I*, Geom. Funct.
  Anal. 9 (1999), Section 2 (exact embeddings and the transfer map).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Liouville domains and their completions).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953.
-/

public section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M E' H' M' E'' H'' M'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' (⊤ : ℕ∞) M']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M''] [ChartedSpace H'' M'']
  [IsManifold I'' (⊤ : ℕ∞) M'']
  {α : SmoothForm I M ℝ 1} {W : Set M} {α' : SmoothForm I' M' ℝ 1} {W' : Set M'}
  {α'' : SmoothForm I'' M'' ℝ 1} {W'' : Set M''} {φ : M → M'} {φ' : M' → M''}
  {h : M → ℝ} {h' : M' → ℝ}

variable (α W α' W') in
/-- A map `φ : M → M'` is an **exact codimension-zero embedding** of `W ⊆ M`, with one-form `α`,
into `W' ⊆ M'`, with one-form `α'`, with **primitive** `h : M → ℝ`, when `φ` is smooth, a local
diffeomorphism at every point of `W`, injective on `W`, and carries `W` into the interior of `W'`,
and when `h` is smooth and `φ^* α' = α + dh` on a neighbourhood of `W`. It is meant for Liouville
domains `W` and `W'` with Liouville primitives `α` and `α'` (`TauCeti.IsLiouvilleDomain`). -/
structure IsExactLiouvilleEmbedding (φ : M → M') (h : M → ℝ) : Prop where
  /-- An exact codimension-zero embedding is a smooth map of the ambient manifolds. -/
  contMDiff : ContMDiff I I' (⊤ : ℕ∞) φ
  /-- An exact codimension-zero embedding is a local diffeomorphism along the domain. -/
  isLocalDiffeomorphOn : IsLocalDiffeomorphOn I I' (⊤ : ℕ∞) φ W
  /-- An exact codimension-zero embedding is injective on the domain. -/
  injOn : InjOn φ W
  /-- An exact codimension-zero embedding carries the domain into the interior of the target. -/
  mapsTo_interior : MapsTo φ W (interior W')
  /-- The primitive of an exact codimension-zero embedding is smooth. -/
  contMDiff_primitive : ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) h
  /-- Near the domain, an exact codimension-zero embedding pulls `α'` back to `α + dh`. -/
  eventually_mpullback_eq : ∀ᶠ x in 𝓝ˢ W,
    mpullback I I' φ α'.1 x = α.1 x + mextDeriv (RoughForm.ofFunction I h) x

/-- The defining properties of an exact codimension-zero embedding. -/
theorem isExactLiouvilleEmbedding_iff : IsExactLiouvilleEmbedding α W α' W' φ h ↔
    ContMDiff I I' (⊤ : ℕ∞) φ ∧ IsLocalDiffeomorphOn I I' (⊤ : ℕ∞) φ W ∧ InjOn φ W ∧
      MapsTo φ W (interior W') ∧ ContMDiff I 𝓘(ℝ) (⊤ : ℕ∞) h ∧
      ∀ᶠ x in 𝓝ˢ W, mpullback I I' φ α'.1 x = α.1 x + mextDeriv (RoughForm.ofFunction I h) x :=
  ⟨fun hφ ↦ ⟨hφ.1, hφ.2, hφ.3, hφ.4, hφ.5, hφ.6⟩,
    fun hφ ↦ ⟨hφ.1, hφ.2.1, hφ.2.2.1, hφ.2.2.2.1, hφ.2.2.2.2.1, hφ.2.2.2.2.2⟩⟩

/-- **The identity is an exact embedding.** If `W` lies in the interior of `W'`, then the identity
of `M` is an exact codimension-zero embedding of `W` into `W'` for the same one-form, with
primitive `0`. -/
theorem isExactLiouvilleEmbedding_id {V : Set M} (hW : W ⊆ interior V) :
    IsExactLiouvilleEmbedding α W α V id 0 where
  contMDiff := contMDiff_id
  isLocalDiffeomorphOn x := by
    simpa using (Diffeomorph.refl I M (⊤ : ℕ∞)).isLocalDiffeomorph x
  injOn := injOn_id W
  mapsTo_interior := hW
  contMDiff_primitive := contMDiff_const
  eventually_mpullback_eq := Eventually.of_forall fun x ↦ by
    ext v
    simp [mextDeriv_ofFunction]

namespace IsExactLiouvilleEmbedding

/-- An exact codimension-zero embedding carries the domain into the target. -/
theorem mapsTo (hφ : IsExactLiouvilleEmbedding α W α' W' φ h) : MapsTo φ W W' :=
  hφ.mapsTo_interior.mono_right interior_subset

/-- **Exact embeddings are symplectic.** Near the domain, an exact codimension-zero embedding
pulls `dα'` back to `dα`. For Liouville domains, where `dα = ω` and `dα' = ω'`, it pulls the
symplectic form `ω'` back to `ω`. -/
theorem eventually_mpullback_mextDeriv_eq (hφ : IsExactLiouvilleEmbedding α W α' W' φ h) :
    ∀ᶠ x in 𝓝ˢ W, mpullback I I' φ (mextDeriv α'.1) x = mextDeriv α.1 x := by
  have hdh : IsSmoothForm I (⊤ : ℕ∞) (mextDeriv (RoughForm.ofFunction I h)) :=
    isSmoothForm_mextDeriv (isSmoothForm_ofFunction_iff.mpr hφ.contMDiff_primitive) (by simp)
  filter_upwards [hφ.eventually_mpullback_eq.eventually_nhdsSet] with x hx
  -- `φ^* dα' = d(φ^* α') = d(α + dh) = dα + d(dh) = dα` at `x`.
  rw [mpullback_mextDeriv_at (hφ.contMDiff.contMDiffAt.of_le (by simp))
      ((α'.contMDiff (φ x)).of_le (by simp)),
    mextDeriv_congr_of_eventuallyEq (η := α.1 + mextDeriv (RoughForm.ofFunction I h)) hx,
    mextDeriv_add ((α.isSmoothForm.contDiffWithinAt_inChartAt_self x).differentiableWithinAt
        (by simp)) ((hdh.contDiffWithinAt_inChartAt_self x).differentiableWithinAt (by simp)),
    mextDeriv_mextDeriv_ofFunction (hφ.contMDiff_primitive.of_le (by simp)), Pi.zero_apply,
    add_zero]

/-- **An exact embedding is an embedding of a neighbourhood.** An exact codimension-zero
embedding of a compact domain `W` into a Hausdorff manifold is injective, and a local
diffeomorphism, on an open neighbourhood of `W`. -/
theorem exists_isOpen_injOn [T2Space M'] (hφ : IsExactLiouvilleEmbedding α W α' W' φ h)
    (hW : IsCompact W) :
    ∃ U, IsOpen U ∧ W ⊆ U ∧ InjOn φ U ∧ IsLocalDiffeomorphOn I I' (⊤ : ℕ∞) φ U := by
  -- Near each point of `W`, `φ` has a left inverse, so it is injective there.
  obtain ⟨t, ht, hinj⟩ := hφ.injOn.exists_mem_nhdsSet hW
    (fun x _ ↦ hφ.contMDiff.continuous.continuousAt) fun x hx ↦ by
      have hf := hφ.isLocalDiffeomorphOn ⟨x, hx⟩
      exact ⟨_, hf.localInverse_eventuallyEq_left, fun a ha b hb hab ↦
        ha.symm.trans ((congrArg hf.localInverse hab).trans hb)⟩
  have hloc : ∀ᶠ y in 𝓝ˢ W, IsLocalDiffeomorphAt I I' (⊤ : ℕ∞) φ y :=
    eventually_nhdsSet_iff_forall.mpr fun x hx ↦ (hφ.isLocalDiffeomorphOn ⟨x, hx⟩).eventually
  obtain ⟨U, hUo, hWU, hU⟩ := mem_nhdsSet_iff_exists.mp (inter_mem ht hloc)
  exact ⟨U, hUo, hWU, hinj.mono fun y hy ↦ (hU hy).1, fun y ↦ (hU y.2).2⟩

/-- **Composition of exact embeddings.** If `φ` is an exact codimension-zero embedding of `W`
into `W'` with primitive `h`, and `φ'` one of `W'` into `W''` with primitive `h'`, then `φ' ∘ φ`
is one of `W` into `W''`, with primitive `h + h' ∘ φ`. -/
theorem comp (hφ' : IsExactLiouvilleEmbedding α' W' α'' W'' φ' h')
    (hφ : IsExactLiouvilleEmbedding α W α' W' φ h) :
    IsExactLiouvilleEmbedding α W α'' W'' (φ' ∘ φ) (h + h' ∘ φ) where
  contMDiff := hφ'.contMDiff.comp hφ.contMDiff
  isLocalDiffeomorphOn x :=
    IsLocalDiffeomorphAt.comp (K := I'') (P := M'') (hφ.isLocalDiffeomorphOn x)
      (hφ'.isLocalDiffeomorphOn ⟨φ x, hφ.mapsTo x.2⟩)
  injOn := hφ'.injOn.comp hφ.injOn hφ.mapsTo
  mapsTo_interior := hφ'.mapsTo_interior.comp hφ.mapsTo
  contMDiff_primitive := hφ.contMDiff_primitive.add (hφ'.contMDiff_primitive.comp hφ.contMDiff)
  eventually_mpullback_eq := by
    have hφd : MDifferentiable I I' φ := hφ.contMDiff.mdifferentiable (by simp)
    have hhd : MDifferentiable I 𝓘(ℝ) h := hφ.contMDiff_primitive.mdifferentiable (by simp)
    have hh'd : MDifferentiable I' 𝓘(ℝ) h' := hφ'.contMDiff_primitive.mdifferentiable (by simp)
    -- Near `W`, the point `φ x` lies near `W'`, where `φ'^* α'' = α' + dh'`.
    have hφ'x : ∀ᶠ x in 𝓝ˢ W, mpullback I' I'' φ' α''.1 (φ x) =
        α'.1 (φ x) + mextDeriv (RoughForm.ofFunction I' h') (φ x) :=
      eventually_nhdsSet_iff_forall.mpr fun x hx ↦
        hφ.contMDiff.continuous.continuousAt.eventually
          (eventually_nhdsSet_iff_forall.mp hφ'.eventually_mpullback_eq _ (hφ.mapsTo hx))
    filter_upwards [hφ.eventually_mpullback_eq, hφ'x] with x hx hx'
    -- `(φ' ∘ φ)^* α'' = φ^* (α' + dh') = α + dh + d(h' ∘ φ)` at `x`.
    have hpull : mpullback I I' φ (mpullback I' I'' φ' α''.1) x =
        mpullback I I' φ (α'.1 + mextDeriv (RoughForm.ofFunction I' h')) x := by
      ext v
      simp only [mpullback_apply, hx', Pi.add_apply]
    rw [mpullback_comp_at (hφd x) ((hφ'.contMDiff.mdifferentiable (by simp)) (φ x)), hpull,
      mpullback_add, Pi.add_apply, hx, mpullback_mextDeriv_ofFunction_apply (hφd x) (hh'd _),
      mextDeriv_ofFunction_add hhd (hh'd.comp hφd), Pi.add_apply, add_assoc]

end IsExactLiouvilleEmbedding

end TauCeti
