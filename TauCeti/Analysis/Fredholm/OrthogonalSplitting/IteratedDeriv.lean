/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Fredholm.OrthogonalSplitting
import TauCeti.Analysis.Calculus.IteratedDeriv.Leibniz
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Iterated derivatives of the orthogonal kernel projections and right inverses

Let `T t : E →L[ℝ] F` be a family of real operators between Banach spaces, `C^n` at `t₀`, with
`T t₀` Fredholm and onto, and let `ι : E →L[ℝ] H` be injective into a Hilbert space. Write `π t`
for the projection onto `ker (T t)` along its `ι`-orthogonal complement
(`ContinuousLinearMap.orthogonalKerProjection`) and `Q t` for the right inverse of `T t` with
values in that complement (`ContinuousLinearMap.orthogonalRightInverse`), and `Tᵢ`, `πᵢ`, `Qᵢ` for
the `i`-th derivatives of `T`, `π`, `Q` at `t₀`. Near `t₀` these satisfy

`T t ∘ Q t = 1`,  `T t ∘ π t = 0`,  `π t ∘ π t = π t`,
`⟪ι (Q t y), ι (π t e)⟫ = 0`,  `⟪ι (π t e), ι e'⟫ = ⟪ι e, ι (π t e')⟫`,

the last because an orthogonal projection is symmetric for the `ι`-pairing
(`ContinuousLinearMap.IsOrthogonalKerProjection.inner_apply_comm`). Differentiating each identity
`n` times by Leibniz's rule (`ContinuousLinearMap.iteratedDeriv_of_bilinear`) gives the identities
of this file, which determine `Qₙ` and `πₙ` from the derivatives of lower order:

* `T₀ (Qₙ y) = -∑_{i < n} (n choose i) T_(n-i) (Qᵢ y)` for `n ≥ 1`, so the component of `Qₙ y`
  in the `ι`-orthogonal complement of `ker T₀` is
  `Qₙ y - π₀ (Qₙ y) = -Q₀ (∑_{i < n} (n choose i) T_(n-i) (Qᵢ y))`
  (`IsFredholm.sub_orthogonalKerProjection_iteratedDeriv_orthogonalRightInverse_apply`);
* its kernel component is determined by the pairings with `k ∈ ker T₀`,
  `⟪ι (Qₙ y), ι k⟫ = -∑_{i < n} (n choose i) ⟪ι (Qᵢ y), ι (π_(n-i) k)⟫`
  (`IsFredholm.inner_iteratedDeriv_orthogonalRightInverse_apply`);
* likewise `πₙ e - π₀ (πₙ e) = -Q₀ (∑_{i < n} (n choose i) T_(n-i) (πᵢ e))`
  (`IsFredholm.sub_orthogonalKerProjection_iteratedDeriv_orthogonalKerProjection_apply`);
* on the kernel, `π₀ (π_(m+1) k) = -∑_{i < m} (m + 1 choose i + 1) π_(i+1) (π_(m-i) k)`
  (`IsFredholm.orthogonalKerProjection_iteratedDeriv_orthogonalKerProjection_of_mem_ker`),
  and the pairings of `πₙ` are symmetric
  (`IsFredholm.inner_iteratedDeriv_orthogonalKerProjection_apply_comm`), so the kernel
  component of `πₙ e` is determined by `⟪ι (πₙ e), ι k⟫ = ⟪ι e, ι (πₙ k)⟫` and the two previous
  identities applied to `k`.

These are the identities of every order behind the first- and second-order ones of
`TauCeti.Analysis.Fredholm.OrthogonalSplitting`, stated along a curve: the derivatives are
`iteratedDeriv` in one real parameter. Through them, estimates on `Q₀`, `π₀` and the derivatives
of `T` pass to the derivatives of every order of the orthogonal splitting, by induction on the
order.

## Main results

* `IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalRightInverse_apply`,
  `IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalKerProjection_apply`,
  `IsFredholm.sum_inner_iteratedDeriv_orthogonalRightInverse_orthogonalKerProjection`
  and
  `IsFredholm.sum_iteratedDeriv_orthogonalKerProjection_apply_apply`:
  the differentiated identities, as Leibniz sums.
* The component identities listed above.
-/

public section

open Function Filter Topology
open scoped InnerProductSpace

namespace ContinuousLinearMap

section IteratedDeriv

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : E →L[ℝ] H} {T : ℝ → E →L[ℝ] F} {t₀ : ℝ} {n : ℕ}

/-- **Leibniz's rule for `T ∘ Q = 1`.** Let `T` be a family of real operators, `C^n` at `t₀`, where
`T t₀` is Fredholm and onto, and `Q t` the right inverse of `T t` with values `ι`-orthogonal to its
kernel. For `n ≠ 0`, `∑_{i ≤ n} (n choose i) T_(n-i) (Qᵢ y) = 0`, where `Tⱼ` and `Qⱼ` are the
`j`-th derivatives of `T` and `Q` at `t₀`. -/
theorem IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalRightInverse_apply
    (hι : Injective ι) (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀))
    (hd : ContDiffAt ℝ n T t₀) (hn : n ≠ 0) (y : F) :
    ∑ i ∈ Finset.range (n + 1), n.choose i • iteratedDeriv (n - i) T t₀
      (iteratedDeriv i (fun t ↦ orthogonalRightInverse ι (T t)) t₀ y) = 0 := by
  have hQ : ContDiffAt ℝ n (fun t ↦ orthogonalRightInverse ι (T t)) t₀ :=
    (hT.contDiffAt_orthogonalRightInverse (n := n) hι hsurj).comp t₀ hd
  have h := (compL ℝ F E F).flip.iteratedDeriv_of_bilinear hQ hd
  -- Near `t₀`, `T t ∘ Q t` is the identity.
  have hid : (fun t ↦ (compL ℝ F E F).flip (orthogonalRightInverse ι (T t)) (T t)) =ᶠ[𝓝 t₀]
      fun _ ↦ ContinuousLinearMap.id ℝ F := by
    filter_upwards [hd.continuousAt.eventually
        (hT.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse hι hsurj)]
      with t ht
    ext y
    exact ht.2.rightInverse y
  simp only [hid.iteratedDeriv_eq n, iteratedDeriv_const, hn, ↓reduceIte] at h
  simpa using (DFunLike.congr_fun h y).symm

/-- **Leibniz's rule for `T ∘ π = 0`.** In the setting of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalRightInverse_apply`,
with `π t` the projection onto `ker (T t)` along its `ι`-orthogonal complement,
`∑_{i ≤ n} (n choose i) T_(n-i) (πᵢ e) = 0` for every `n`. -/
theorem IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalKerProjection_apply
    (hι : Injective ι) (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀))
    (hd : ContDiffAt ℝ n T t₀) (e : E) :
    ∑ i ∈ Finset.range (n + 1), n.choose i • iteratedDeriv (n - i) T t₀
      (iteratedDeriv i (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e) = 0 := by
  have hπ : ContDiffAt ℝ n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ :=
    (hT.contDiffAt_orthogonalKerProjection (n := n) hι hsurj).comp t₀ hd
  have h := (compL ℝ E E F).flip.iteratedDeriv_of_bilinear hπ hd
  -- Near `t₀`, `T t ∘ π t` vanishes.
  have h0 : (fun t ↦ (compL ℝ E E F).flip (orthogonalKerProjection ι (T t)) (T t)) =ᶠ[𝓝 t₀]
      fun _ ↦ 0 := by
    filter_upwards [hd.continuousAt.eventually
        (hT.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse hι hsurj)]
      with t ht
    ext e
    exact LinearMap.mem_ker.1 (ht.1.mem_ker e)
  simp only [h0.iteratedDeriv_eq n, iteratedDeriv_const, ite_self] at h
  simpa using (DFunLike.congr_fun h e).symm

/-- **Leibniz's rule for the orthogonality of `Q` to the kernel.** In the setting of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalRightInverse_apply`,
`∑_{i ≤ n} (n choose i) ⟪ι (Qᵢ y), ι (π_(n-i) e)⟫ = 0` for every `n`, since
`⟪ι (Q t y), ι (π t e)⟫ = 0` near `t₀`. -/
theorem IsFredholm.sum_inner_iteratedDeriv_orthogonalRightInverse_orthogonalKerProjection
    (hι : Injective ι) (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀))
    (hd : ContDiffAt ℝ n T t₀) (y : F) (e : E) :
    ∑ i ∈ Finset.range (n + 1), n.choose i •
      ⟪ι (iteratedDeriv i (fun t ↦ orthogonalRightInverse ι (T t)) t₀ y),
        ι (iteratedDeriv (n - i) (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e)⟫_ℝ = 0 := by
  have hQ : ContDiffAt ℝ n (fun t ↦ orthogonalRightInverse ι (T t)) t₀ :=
    (hT.contDiffAt_orthogonalRightInverse (n := n) hι hsurj).comp t₀ hd
  have hπ : ContDiffAt ℝ n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ :=
    (hT.contDiffAt_orthogonalKerProjection (n := n) hι hsurj).comp t₀ hd
  set B : (F →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ι.comp (apply ℝ E y)) (ι.comp (apply ℝ E e))
  have h := B.iteratedDeriv_of_bilinear hQ hπ
  -- Near `t₀`, the values of `Q t` are `ι`-orthogonal to the kernel of `T t`.
  have h0 : (fun t ↦ B (orthogonalRightInverse ι (T t)) (orthogonalKerProjection ι (T t)))
      =ᶠ[𝓝 t₀] fun _ ↦ 0 := by
    filter_upwards [hd.continuousAt.eventually
        (hT.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse hι hsurj)]
      with t ht
    simpa [B] using ht.2.inner_eq_zero y _ (ht.1.mem_ker e)
  simp only [h0.iteratedDeriv_eq n, iteratedDeriv_const, ite_self] at h
  simpa [B] using h.symm

/-- **Leibniz's rule for `π ∘ π = π`.** In the setting of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalKerProjection_apply`,
`∑_{i ≤ n} (n choose i) πᵢ (π_(n-i) e) = πₙ e` for every `n`. -/
theorem IsFredholm.sum_iteratedDeriv_orthogonalKerProjection_apply_apply
    (hι : Injective ι) (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀))
    (hd : ContDiffAt ℝ n T t₀) (e : E) :
    ∑ i ∈ Finset.range (n + 1), n.choose i •
      iteratedDeriv i (fun t ↦ orthogonalKerProjection ι (T t)) t₀
        (iteratedDeriv (n - i) (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e) =
      iteratedDeriv n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e := by
  have hπ : ContDiffAt ℝ n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ :=
    (hT.contDiffAt_orthogonalKerProjection (n := n) hι hsurj).comp t₀ hd
  have h := (compL ℝ E E E).iteratedDeriv_of_bilinear hπ hπ
  -- Near `t₀`, `π t` is idempotent.
  have hidem : (fun t ↦ compL ℝ E E E (orthogonalKerProjection ι (T t))
      (orthogonalKerProjection ι (T t))) =ᶠ[𝓝 t₀] fun t ↦ orthogonalKerProjection ι (T t) := by
    filter_upwards [hd.continuousAt.eventually
        (hT.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse hι hsurj)]
      with t ht
    ext e
    exact ht.1.apply_of_mem_ker hι (ht.1.mem_ker e)
  rw [hidem.iteratedDeriv_eq n] at h
  simpa using (DFunLike.congr_fun h e).symm

/-- **The derivatives of the orthogonal kernel projections are symmetric:**
`⟪ι (πₙ e), ι e'⟫ = ⟪ι e, ι (πₙ e')⟫` for every `n`, in the setting of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalKerProjection_apply`. -/
theorem IsFredholm.inner_iteratedDeriv_orthogonalKerProjection_apply_comm (hι : Injective ι)
    (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀)) (hd : ContDiffAt ℝ n T t₀)
    (e e' : E) :
    ⟪ι (iteratedDeriv n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e), ι e'⟫_ℝ =
      ⟪ι e, ι (iteratedDeriv n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e')⟫_ℝ := by
  have hπ : ContDiffAt ℝ n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ :=
    (hT.contDiffAt_orthogonalKerProjection (n := n) hι hsurj).comp t₀ hd
  set L : (E →L[ℝ] E) →L[ℝ] ℝ := (innerSL ℝ (ι e')).comp (ι.comp (apply ℝ E e)) -
    (innerSL ℝ (ι e)).comp (ι.comp (apply ℝ E e'))
  -- Near `t₀`, `L (π t) = ⟪ι (π t e), ι e'⟫ - ⟪ι e, ι (π t e')⟫` vanishes.
  have h0 : (L ∘ fun t ↦ orthogonalKerProjection ι (T t)) =ᶠ[𝓝 t₀] fun _ ↦ 0 := by
    filter_upwards [hd.continuousAt.eventually
        (hT.eventually_isOrthogonalKerProjection_and_isOrthogonalRightInverse hι hsurj)]
      with t ht
    simp only [L, Function.comp_apply, sub_apply, coe_comp, apply_apply, innerSL_apply_apply]
    rw [real_inner_comm, ht.1.inner_apply_comm e e', sub_self]
  have h := L.iteratedDeriv_comp_left hπ le_rfl
  simp only [h0.iteratedDeriv_eq n, iteratedDeriv_const, ite_self] at h
  simp only [L, sub_apply, coe_comp, Function.comp_apply, apply_apply, innerSL_apply_apply]
    at h
  rw [real_inner_comm, ← sub_eq_zero, h]

/-- **The complement component of the iterated derivatives of the right inverses.** In the setting
of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalRightInverse_apply`,
for `n ≠ 0` the component of `Qₙ y` in the `ι`-orthogonal complement of `ker (T t₀)` is

`Qₙ y - π₀ (Qₙ y) = -Q₀ (∑_{i < n} (n choose i) T_(n-i) (Qᵢ y))`. -/
theorem IsFredholm.sub_orthogonalKerProjection_iteratedDeriv_orthogonalRightInverse_apply
    (hι : Injective ι) (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀))
    (hd : ContDiffAt ℝ n T t₀) (hn : n ≠ 0) (y : F) :
    iteratedDeriv n (fun t ↦ orthogonalRightInverse ι (T t)) t₀ y -
        orthogonalKerProjection ι (T t₀)
          (iteratedDeriv n (fun t ↦ orthogonalRightInverse ι (T t)) t₀ y) =
      -orthogonalRightInverse ι (T t₀) (∑ i ∈ Finset.range n, n.choose i •
        iteratedDeriv (n - i) T t₀
          (iteratedDeriv i (fun t ↦ orthogonalRightInverse ι (T t)) t₀ y)) := by
  have h := hT.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalRightInverse_apply
    hι hsurj hd hn y
  rw [Finset.sum_range_succ, Nat.choose_self, one_smul, Nat.sub_self, iteratedDeriv_zero]
    at h
  rw [hT.sub_orthogonalKerProjection_apply hι hsurj, eq_neg_of_add_eq_zero_right h, map_neg]

/-- **The kernel pairings of the iterated derivatives of the right inverses.** In the setting of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalRightInverse_apply`,
for `k` in the kernel of `T t₀`,

`⟪ι (Qₙ y), ι k⟫ = -∑_{i < n} (n choose i) ⟪ι (Qᵢ y), ι (π_(n-i) k)⟫`. -/
theorem IsFredholm.inner_iteratedDeriv_orthogonalRightInverse_apply (hι : Injective ι)
    (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀)) (hd : ContDiffAt ℝ n T t₀) (y : F)
    {k : E} (hk : k ∈ (T t₀).ker) :
    ⟪ι (iteratedDeriv n (fun t ↦ orthogonalRightInverse ι (T t)) t₀ y), ι k⟫_ℝ =
      -∑ i ∈ Finset.range n, n.choose i •
        ⟪ι (iteratedDeriv i (fun t ↦ orthogonalRightInverse ι (T t)) t₀ y),
          ι (iteratedDeriv (n - i) (fun t ↦ orthogonalKerProjection ι (T t)) t₀ k)⟫_ℝ := by
  have := hT.finite_ker
  have h :=
    hT.sum_inner_iteratedDeriv_orthogonalRightInverse_orthogonalKerProjection
      hι hsurj hd y k
  rw [Finset.sum_range_succ, Nat.choose_self, one_smul, Nat.sub_self, iteratedDeriv_zero,
    (isOrthogonalKerProjection_orthogonalKerProjection hι (T t₀)).apply_of_mem_ker hι hk] at h
  exact eq_neg_of_add_eq_zero_right h

/-- **The complement component of the iterated derivatives of the kernel projections.** In the
setting of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalKerProjection_apply`,
the component of `πₙ e` in the `ι`-orthogonal complement of `ker (T t₀)` is

`πₙ e - π₀ (πₙ e) = -Q₀ (∑_{i < n} (n choose i) T_(n-i) (πᵢ e))`. -/
theorem IsFredholm.sub_orthogonalKerProjection_iteratedDeriv_orthogonalKerProjection_apply
    (hι : Injective ι) (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀))
    (hd : ContDiffAt ℝ n T t₀) (e : E) :
    iteratedDeriv n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e -
        orthogonalKerProjection ι (T t₀)
          (iteratedDeriv n (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e) =
      -orthogonalRightInverse ι (T t₀) (∑ i ∈ Finset.range n, n.choose i •
        iteratedDeriv (n - i) T t₀
          (iteratedDeriv i (fun t ↦ orthogonalKerProjection ι (T t)) t₀ e)) := by
  have h := hT.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalKerProjection_apply
    hι hsurj hd e
  rw [Finset.sum_range_succ, Nat.choose_self, one_smul, Nat.sub_self, iteratedDeriv_zero]
    at h
  rw [hT.sub_orthogonalKerProjection_apply hι hsurj, eq_neg_of_add_eq_zero_right h, map_neg]

/-- **The kernel component of the iterated derivatives of the kernel projections on the
kernel.** In the setting of
`IsFredholm.sum_iteratedDeriv_apply_iteratedDeriv_orthogonalKerProjection_apply`,
for `k` in the kernel of `T t₀`,

`π₀ (π_(m+1) k) = -∑_{i < m} (m + 1 choose i + 1) π_(i+1) (π_(m-i) k)`.

In particular `π₀ (π' k) = 0`. -/
theorem IsFredholm.orthogonalKerProjection_iteratedDeriv_orthogonalKerProjection_of_mem_ker
    (hι : Injective ι) (hT : IsFredholm (T t₀)) (hsurj : Surjective (T t₀)) {m : ℕ}
    (hd : ContDiffAt ℝ (m + 1) T t₀) {k : E} (hk : k ∈ (T t₀).ker) :
    orthogonalKerProjection ι (T t₀)
        (iteratedDeriv (m + 1) (fun t ↦ orthogonalKerProjection ι (T t)) t₀ k) =
      -∑ i ∈ Finset.range m, (m + 1).choose (i + 1) •
        iteratedDeriv (i + 1) (fun t ↦ orthogonalKerProjection ι (T t)) t₀
          (iteratedDeriv (m - i) (fun t ↦ orthogonalKerProjection ι (T t)) t₀ k) := by
  have := hT.finite_ker
  have h :=
    hT.sum_iteratedDeriv_orthogonalKerProjection_apply_apply
      hι hsurj hd k
  -- The top term `π_(m+1) (π₀ k) = π_(m+1) k` cancels the right side, and the bottom term is
  -- `π₀ (π_(m+1) k)`.
  rw [Finset.sum_range_succ, Nat.choose_self, one_smul, Nat.sub_self, iteratedDeriv_zero,
    (isOrthogonalKerProjection_orthogonalKerProjection hι (T t₀)).apply_of_mem_ker hι hk,
    add_eq_right, Finset.sum_range_succ', Nat.choose_zero_right, one_smul, Nat.sub_zero,
    iteratedDeriv_zero] at h
  have hs : ∑ i ∈ Finset.range m, (m + 1).choose (i + 1) •
      iteratedDeriv (i + 1) (fun t ↦ orthogonalKerProjection ι (T t)) t₀
        (iteratedDeriv (m + 1 - (i + 1)) (fun t ↦ orthogonalKerProjection ι (T t)) t₀ k) =
      ∑ i ∈ Finset.range m, (m + 1).choose (i + 1) •
        iteratedDeriv (i + 1) (fun t ↦ orthogonalKerProjection ι (T t)) t₀
          (iteratedDeriv (m - i) (fun t ↦ orthogonalKerProjection ι (T t)) t₀ k) :=
    Finset.sum_congr rfl fun i _ ↦ by rw [Nat.add_sub_add_right]
  rw [hs] at h
  exact eq_neg_of_add_eq_zero_right h

end IteratedDeriv

end ContinuousLinearMap
