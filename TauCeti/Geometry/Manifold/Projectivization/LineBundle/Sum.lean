/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Projectivization.LineBundle

/-!
# Direct sums of the line bundles `𝒪(k)` on projective space

For a finite family of integers `k : κ → ℤ`, the vector bundle `⨁ₗ 𝒪(k l)` on projective space
`ℙ 𝕜 (Fin (n + 1) → 𝕜)` is glued, like each `𝒪(k)` (`Projectivization.twistCore`), from the trivial
bundles with fibre `κ → 𝕜` over the standard affine opens `U_i`, now along the diagonal transition
functions `c ↦ (l ↦ (v i / v j) ^ (k l) * c l)` on `U_i ∩ U_j`. It is the Mathlib vector-bundle
core `Projectivization.twistSumCore k`, with model fibre `κ → 𝕜`; the coordinate `c l` of a vector
in the frame of the chart `i` is its component in the summand `𝒪(k l)`. The transitions are
analytic, so it is an analytic vector bundle (`Projectivization.isContMDiff_twistSumCore`).

The summands are visible on total spaces: the projection onto the summand `l` and the inclusion of
the summand `l` are analytic maps between the total spaces of `⨁ₗ 𝒪(k l)` and of `𝒪(k l)`
(`Projectivization.contMDiff_twistSumCore_apply`,
`Projectivization.contMDiff_twistSumCore_single`), since in every frame they are the coordinate
projection and the coordinate inclusion.

Split bundles of this form are the normal forms of holomorphic bundles on the projective line, and
the restriction of the tangent bundle of `ℙⁿ` to the coordinate line is `𝒪(2) ⊕ 𝒪(1)ⁿ⁻¹`
(`Projectivization.coordLineTangentDiffeomorph`, in
`TauCeti.Geometry.Manifold.Projectivization.LineBundle.Tangent`).

## Main declarations

* `Projectivization.twistSumCore k`: the vector-bundle core of `⨁ₗ 𝒪(k l)`.
* `Projectivization.isContMDiff_twistSumCore`: it is an analytic vector bundle.
* `Projectivization.contMDiff_twistSumCore_apply`: the projection onto a summand is analytic.
* `Projectivization.contMDiff_twistSumCore_single`: the inclusion of a summand is analytic.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0, §5
  (vector bundles given by transition functions).
* C. Okonek, M. Schneider and H. Spindler, *Vector Bundles on Complex Projective Spaces*,
  Birkhäuser, 1980, Chapter I, §2 (split bundles).
-/

public noncomputable section

open Bundle Set
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ} {κ : Type*} [Fintype κ]

/-- The vector bundle `⨁ₗ 𝒪(k l)` on projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, as a Mathlib
vector-bundle core with model fibre `κ → 𝕜`. The chart `i` is trivial over the standard affine open
`U_i`, the coordinate change from the chart `i` to the chart `j` multiplies the coordinate `l` by
`twistTransition (k l) i j`, the transition of `𝒪(k l)`, and the preferred chart at `x` is the one
used by `chartAt`, as for `Projectivization.twistCore`. -/
def twistSumCore (k : κ → ℤ) :
    VectorBundleCore 𝕜 (ℙ 𝕜 (Fin (n + 1) → 𝕜)) (κ → 𝕜) (Fin (n + 1)) where
  baseSet i := affineOpen i
  isOpen_baseSet i := isOpen_affineOpen i
  indexAt x := (exists_mem_affineOpen x).choose
  mem_baseSet_at x := (exists_mem_affineOpen x).choose_spec
  coordChange i j x := ContinuousLinearMap.mul 𝕜 (κ → 𝕜) fun l ↦ twistTransition (k l) i j x
  coordChange_self i x hx v := by
    ext l
    simp [twistTransition_self _ hx]
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.mul 𝕜 (κ → 𝕜)).continuous.comp_continuousOn <|
      continuousOn_pi.2 fun l ↦ (contMDiffOn_twistTransition (k l) i j 0).continuousOn
  coordChange_comp i j l x hx v := by
    ext l'
    simp only [ContinuousLinearMap.mul_apply', Pi.mul_apply, ← mul_assoc]
    rw [twistTransition_mul_twistTransition _ i l hx.1.2]

variable (k : κ → ℤ)

/-- The chart `i` of `⨁ₗ 𝒪(k l)` is defined over the standard affine open `U_i`. It is not a simp
lemma, since `VectorBundleCore.baseSet_at` already rewrites its left side into the left side of
`twistSumCore_localTriv_baseSet`. -/
theorem twistSumCore_baseSet (i : Fin (n + 1)) :
    (twistSumCore (𝕜 := 𝕜) k).baseSet i = affineOpen i :=
  (rfl)

/-- The chart `i` of `⨁ₗ 𝒪(k l)` is trivial over the standard affine open `U_i`. -/
@[simp]
theorem twistSumCore_localTriv_baseSet (i : Fin (n + 1)) :
    ((twistSumCore (𝕜 := 𝕜) k).localTriv i).baseSet = affineOpen i :=
  (rfl)

/-- A point lies in the affine open of its preferred chart. -/
theorem mem_affineOpen_twistSumCore_indexAt (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    x ∈ affineOpen ((twistSumCore (𝕜 := 𝕜) k).indexAt x) := by
  rw [← twistSumCore_baseSet k]
  exact (twistSumCore k).mem_baseSet_at x

/-- The preferred chart of `⨁ₗ 𝒪(k l)` at `x` is the affine open chosen by
`exists_mem_affineOpen`, as for each `𝒪(k')` (`Projectivization.twistCore_indexAt`). -/
theorem twistSumCore_indexAt (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    (twistSumCore (𝕜 := 𝕜) k).indexAt x = (exists_mem_affineOpen x).choose :=
  (rfl)

/-- The coordinate change of `⨁ₗ 𝒪(k l)` from the chart `i` to the chart `j` multiplies the
coordinate `l` by the transition of `𝒪(k l)`. -/
@[simp]
theorem twistSumCore_coordChange_apply (i j : Fin (n + 1)) (x : ℙ 𝕜 (Fin (n + 1) → 𝕜))
    (v : κ → 𝕜) (l : κ) :
    (twistSumCore k).coordChange i j x v l = twistTransition (k l) i j x * v l :=
  (rfl)

/-- In the trivialization of `⨁ₗ 𝒪(k l)` at `x₀`, a vector at `x` is read by the coordinate change
from the preferred chart at `x` to the preferred chart at `x₀`. -/
theorem twistSumCore_trivializationAt_snd (x₀ x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (v : κ → 𝕜) :
    (trivializationAt (κ → 𝕜) (twistSumCore k).Fiber x₀ ⟨x, v⟩).2 =
      (twistSumCore k).coordChange ((twistSumCore k).indexAt x) ((twistSumCore k).indexAt x₀) x v :=
  (rfl)

/-- In the trivialization of `⨁ₗ 𝒪(k l)` at `x₀`, the coordinate `l` of a vector at `x` is its
coordinate `l` in the frame of the preferred chart at `x`, multiplied by the transition of
`𝒪(k l)` to the preferred chart at `x₀`. -/
theorem twistSumCore_trivializationAt_apply_snd (x₀ x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) (v : κ → 𝕜)
    (l : κ) :
    (trivializationAt (κ → 𝕜) (twistSumCore k).Fiber x₀ ⟨x, v⟩).2 l =
      twistTransition (k l) ((twistSumCore k).indexAt x) ((twistSumCore k).indexAt x₀) x * v l :=
  (rfl)

/-- **`⨁ₗ 𝒪(k l)` is an analytic vector bundle.** Its transition functions are analytic, so for
`𝕜 = ℂ` it is a holomorphic vector bundle on `ℂℙⁿ`. -/
instance isContMDiff_twistSumCore :
    (twistSumCore (𝕜 := 𝕜) (n := n) k).IsContMDiff 𝓘(𝕜, Fin n → 𝕜) ω where
  contMDiffOn_coordChange i j :=
    (ContinuousLinearMap.mul 𝕜 (κ → 𝕜)).contMDiff.comp_contMDiffOn <|
      contMDiffOn_pi_module_iff.2 fun l ↦ contMDiffOn_twistTransition (k l) i j ω

/-! ### The summands -/

/-- **The projection onto a summand is analytic.** The map of total spaces from `⨁ₗ 𝒪(k l)` to
`𝒪(k l)` taking a vector to its component `l` is analytic, and so `C^r` for every `r`. -/
theorem contMDiff_twistSumCore_apply (l : κ) {r : ℕ∞ω} :
    ContMDiff (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, κ → 𝕜)) (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜)) r
      (fun p : TotalSpace (κ → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := n) k).Fiber ↦
        TotalSpace.mk' 𝕜 (E := (twistCore (k l)).Fiber) p.proj (p.snd l)) := by
  refine ContMDiff.of_le (fun p ↦ ?_) le_top
  have hid := (Bundle.contMDiffAt_totalSpace_iff (n := ω) (IB := 𝓘(𝕜, Fin n → 𝕜))
    (IM := 𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, κ → 𝕜))
    (f := fun q : TotalSpace (κ → 𝕜) (twistSumCore (𝕜 := 𝕜) (n := n) k).Fiber ↦ q)
    (x₀ := p)).1 contMDiffAt_id
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hid.1, ?_⟩
  -- In the frames of the preferred chart at `p.proj`, the projection is the coordinate `l`.
  refine (((contDiff_apply 𝕜 (fun _ : κ ↦ 𝕜) l).contMDiff.contMDiffAt).comp p
    hid.2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun ⟨x, v⟩ ↦ ?_)
  have h := twistSumCore_trivializationAt_apply_snd k p.proj x v l
  rw [twistSumCore_indexAt, twistSumCore_indexAt, ← twistCore_indexAt (k l),
    ← twistCore_indexAt (k l)] at h
  exact (twistCore_trivializationAt_apply_snd (k l) p.proj x (v l)).trans h.symm

/-- **The inclusion of a summand is analytic.** The map of total spaces from `𝒪(k l)` to
`⨁ₗ 𝒪(k l)` placing a vector in the summand `l` is analytic, and so `C^r` for every `r`. -/
theorem contMDiff_twistSumCore_single [DecidableEq κ] (l : κ) {r : ℕ∞ω} :
    ContMDiff (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜)) (𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜, κ → 𝕜)) r
      (fun p : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (k l)).Fiber ↦
        TotalSpace.mk' (κ → 𝕜) (E := (twistSumCore k).Fiber) p.proj (Pi.single l p.snd)) := by
  refine ContMDiff.of_le (fun p ↦ ?_) le_top
  have hid := (Bundle.contMDiffAt_totalSpace_iff (n := ω) (IB := 𝓘(𝕜, Fin n → 𝕜))
    (IM := 𝓘(𝕜, Fin n → 𝕜).prod 𝓘(𝕜))
    (f := fun q : TotalSpace 𝕜 (twistCore (𝕜 := 𝕜) (n := n) (k l)).Fiber ↦ q)
    (x₀ := p)).1 contMDiffAt_id
  refine Bundle.contMDiffAt_totalSpace_iff.2 ⟨hid.1, ?_⟩
  -- In the frames of the preferred chart at `p.proj`, the inclusion is the coordinate inclusion.
  refine (((ContinuousLinearMap.single 𝕜 (fun _ : κ ↦ 𝕜) l).contMDiff.contMDiffAt).comp p
    hid.2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun ⟨x, c⟩ ↦ ?_)
  ext l'
  refine (twistSumCore_trivializationAt_apply_snd k p.proj x (Pi.single l c) l').trans ?_
  simp only [Function.comp_apply, ContinuousLinearMap.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h
    -- The fibre `(twistCore (k l')).Fiber x` is `𝕜` only up to unfolding, hence `erw`.
    erw [Pi.single_eq_same]
    rw [twistSumCore_indexAt, twistSumCore_indexAt, ← twistCore_indexAt (k l'),
      ← twistCore_indexAt (k l')]
    exact (twistCore_trivializationAt_apply_snd (k l') p.proj x c).symm
  · erw [Pi.single_eq_of_ne h, mul_zero]

end Projectivization
