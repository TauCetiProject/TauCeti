/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.IsManifold.Pi
public import TauCeti.Geometry.Manifold.SymmetricPower.Manifold
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.Complex.InverseFunction
import TauCeti.Topology.Sym.Basic
import TauCeti.Topology.Constructions.Pi

/-!
# The quotient map onto the symmetric power of a complex curve

Let `α` be a Hausdorff one-dimensional complex manifold, such as a Riemann surface `Σ`. Its `n`-th
symmetric power `Sym α n` is a complex manifold for the elementary-symmetric charts
(`TauCeti.isManifold_symChartedSpace`), and the product `αⁿ = Fin n → α` is a complex manifold for
the product charts. The quotient map

`Sym.ofFn : αⁿ → Sym α n`, `(z₁, …, zₙ) ↦ {z₁, …, zₙ}`

forgets the order of the points. This file shows that it is a local biholomorphism exactly at the
tuples of pairwise distinct points (`Sym.isLocalDiffeomorphAt_ofFn_iff`).

* **Off the diagonal.** At a tuple `p` of distinct points, read in the product chart at `p` and in
  any chart of `Sym α n`, the quotient map is a complex analytic function of the product
  coordinates with injective, hence bijective, derivative
  (`TauCeti.exists_injective_hasFDerivAt_symChartAt_ofFn`). So `Sym.ofFn` is holomorphic there
  (`Sym.contMDiffAt_ofFn`), with bijective differential (`Sym.bijective_mfderiv_ofFn`), and the
  holomorphic inverse function theorem makes it a local biholomorphism
  (`Sym.isLocalDiffeomorphAt_ofFn`). The tuples of distinct points form an open set, on which
  `Sym.ofFn` is a local biholomorphism (`Sym.isLocalDiffeomorphOn_ofFn`).
* **On the diagonal.** If `p i = p j` for `i ≠ j`, then `Sym.ofFn` is not injective near `p`: since
  `α` has no isolated points, moving the `i`-th point of `p` slightly to `q ≠ p i` gives a tuple
  `w` near `p`, and swapping its `i`-th and `j`-th points gives a different tuple near `p` with the
  same image (`Sym.frequently_ofFn_eq_ofFn_and_ne`). So `Sym.ofFn` is not injective on any
  neighbourhood of `p`, hence not a local diffeomorphism there
  (`Sym.injective_of_isLocalDiffeomorphAt_ofFn`). For two points of `ℂ`, the
  coordinates `(z₁ + z₂, z₁ z₂)` do not separate `(z₁, z₂)` from `(z₂, z₁)`, and the collision
  `z₁ = z₂` is where these two tuples come together.

The local inverses of `Sym.ofFn` off the diagonal are what carry objects on `αⁿ` that are invariant
under permutations of the factors, such as the sum of the pullbacks of an area form of `Σ` along
the projections, down to the part of `Sym α n` away from the diagonal. That part contains the tori
`T_α = α₁ × ⋯ × α_g` of a Heegaard diagram, whose points are tuples of points on pairwise disjoint
curves.

## Main results

* `Sym.contMDiffAt_ofFn`, `Sym.contMDiffOn_ofFn`: the quotient map is holomorphic, of every
  regularity `C^k` including `C^ω`, at the tuples of distinct points.
* `Sym.bijective_mfderiv_ofFn`: its differential at a tuple of distinct points is bijective.
* `Sym.isLocalDiffeomorphAt_ofFn`, `Sym.isLocalDiffeomorphOn_ofFn`: it is a local biholomorphism at
  the tuples of distinct points.
* `Sym.injective_of_isLocalDiffeomorphAt_ofFn`, `Sym.isLocalDiffeomorphAt_ofFn_iff`: it is a local
  biholomorphism at a tuple exactly when the points of the tuple are distinct.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and topological invariants for closed
  three-manifolds*, Ann. of Math. **159** (2004),
  [arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.2 (the complex structure of
  `Sym^g(Σ)`, for which the quotient map from `Σ^g` is a local biholomorphism off the diagonal).
* T. Perutz, *Hamiltonian handleslides for Heegaard Floer homology*, Proceedings of Gökova
  Geometry-Topology Conference 2007, [arXiv:0801.0564](https://arxiv.org/abs/0801.0564), §1
  (forms on `Sym^g(Σ)` agreeing with the product form near the Heegaard tori).
-/

public section

open Filter Function Set Topology TauCeti
open scoped Manifold ContDiff

namespace Sym

variable {α : Type*} [TopologicalSpace α] [ChartedSpace ℂ α] {n : ℕ} {p : Fin n → α}

/-! ### Off the diagonal: the quotient map in charts -/

section Distinct

variable [T2Space α] [IsManifold 𝓘(ℂ) 1 α]

omit [T2Space α] [IsManifold 𝓘(ℂ) 1 α] in
/-- The point of the product coordinates at a tuple `p` is the tuple of the chart coordinates of
its points. -/
private theorem extChartAt_pi_self_eq (p : Fin n → α) :
    extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) p p = fun j => chartAt ℂ (p j) (p j) :=
  funext fun j => by simp

/-- At a tuple `p` of distinct points, the quotient map read in the product chart at `p` and in the
chosen elementary-symmetric chart at its image is, near the coordinates of `p`, a complex analytic
function with injective derivative. -/
private theorem exists_writtenInExtChartAt_ofFn (hp : Injective p) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    ∃ (T : (Fin n → ℂ) → Fin n → ℂ) (T' : (Fin n → ℂ) →L[ℂ] Fin n → ℂ),
      AnalyticAt ℂ T (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) p p) ∧
      Injective T' ∧ HasFDerivAt T T' (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) p p) ∧
      writtenInExtChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) p Sym.ofFn
        =ᶠ[𝓝 (extChartAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) p p)] T := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  set I := ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)
  obtain ⟨T, T', hTa, hT'inj, hT', hT⟩ :=
    exists_injective_hasFDerivAt_symChartAt_ofFn hp (Sym.ofFn p) (mem_symChartAt_source _)
  rw [← extChartAt_pi_self_eq] at hTa hT'
  refine ⟨T, T', hTa, hT'inj, hT', ?_⟩
  -- the inverse product chart sends coordinates near those of `p` to tuples near `p`
  have hsymm : Tendsto (extChartAt I p).symm (𝓝 (extChartAt I p p)) (𝓝 p) := by
    simpa only [extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := I) p).tendsto
  filter_upwards [extChartAt_target_mem_nhds (I := I) p, hsymm.eventually hT] with u hu hTu
  simp only [writtenInExtChartAt, comp_apply] at hTu ⊢
  simp only [extChartAt_coe, modelWithCornersSelf_coe, symChartedSpace_chartAt, comp_apply,
    id_eq, hTu]
  congr 1
  funext j
  -- the product chart reads the tuple `(extChartAt I p).symm u` back as `u`
  simpa only [extChartAt_coe, modelWithCornersSelf_coe, comp_apply, id_eq] using
    (extChartAt_pi_apply p _ j).symm.trans (congrFun ((extChartAt I p).right_inv hu) j)

/-- **The quotient map onto the symmetric power is holomorphic off the diagonal.** At a tuple of
pairwise distinct points of a Hausdorff complex curve `α`, the map `Sym.ofFn : αⁿ → Sym α n` is
`C^k`, for every `k` including `ω`, for the product charts of `αⁿ` and the elementary-symmetric
charts of `Sym α n`. -/
theorem contMDiffAt_ofFn (hp : Injective p) (k : ℕ∞ω) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    ContMDiffAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) k Sym.ofFn p := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  obtain ⟨T, -, hTa, -, -, hT⟩ := exists_writtenInExtChartAt_ofFn hp
  rw [contMDiffAt_iff, ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ]
  exact ⟨continuous_ofFn.continuousAt, hTa.contDiffAt.congr_of_eventuallyEq hT⟩

/-- The quotient map onto the symmetric power is holomorphic, of every regularity `C^k` including
`C^ω`, on the open set of tuples of pairwise distinct points. -/
theorem contMDiffOn_ofFn (k : ℕ∞ω) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    ContMDiffOn (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) k Sym.ofFn
      {p : Fin n → α | Injective p} := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  exact fun _ hp => (contMDiffAt_ofFn hp k).contMDiffWithinAt

/-- **The differential of the quotient map onto the symmetric power is bijective off the
diagonal.** At a tuple of pairwise distinct points of a Hausdorff complex curve, the complex
differential of `Sym.ofFn : αⁿ → Sym α n` is a bijection between the tangent spaces. -/
theorem bijective_mfderiv_ofFn (hp : Injective p) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    Bijective (mfderiv (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) Sym.ofFn p) := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  obtain ⟨T, T', -, hT'inj, hT', hT⟩ := exists_writtenInExtChartAt_ofFn hp
  have hM : HasMFDerivAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) Sym.ofFn p
      T' := by
    refine ⟨continuous_ofFn.continuousAt, ?_⟩
    rw [ModelWithCorners.Boundaryless.range_eq_univ, hasFDerivWithinAt_univ]
    exact hT'.congr_of_eventuallyEq hT
  rw [hM.mfderiv]
  -- an injective endomorphism of a finite-dimensional space is bijective
  exact ⟨hT'inj, LinearMap.injective_iff_surjective.1 hT'inj⟩

/-- **The quotient map onto the symmetric power is a local biholomorphism off the diagonal.** At a
tuple of pairwise distinct points of a Hausdorff complex curve `α`, the map
`Sym.ofFn : αⁿ → Sym α n` is a local diffeomorphism of class `C^k`, for every `k` including `ω`,
for the product charts of `αⁿ` and the elementary-symmetric charts of `Sym α n`. -/
theorem isLocalDiffeomorphAt_ofFn (hp : Injective p) (k : ℕ∞ω) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    IsLocalDiffeomorphAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) k Sym.ofFn
      p := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  have : IsManifold 𝓘(ℂ, Fin n → ℂ) 1 (Sym α n) :=
    have := isManifold_symChartedSpace (α := α) (n := n)
    .of_le le_top
  exact ((contMDiffOn_ofFn 1).mdifferentiableOn one_ne_zero
    ).isLocalDiffeomorphAt_of_bijective_mfderiv (isOpen_setOf_injective.mem_nhds hp)
    (bijective_mfderiv_ofFn hp)

/-- The quotient map onto the symmetric power of a Hausdorff complex curve is a local
biholomorphism, of class `C^k` for every `k` including `ω`, on the open set of tuples of pairwise
distinct points. -/
theorem isLocalDiffeomorphOn_ofFn (k : ℕ∞ω) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    IsLocalDiffeomorphOn (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) k Sym.ofFn
      {p : Fin n → α | Injective p} := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  exact fun p => isLocalDiffeomorphAt_ofFn p.property k

end Distinct

/-! ### On the diagonal: the quotient map is not locally injective -/

section Diagonal

variable [T2Space α]

/-- If the quotient map `Sym.ofFn : αⁿ → Sym α n` is a `C^k` local diffeomorphism (for `k = ω`, a
local biholomorphism) at a tuple `p`, then the points of `p` are distinct. -/
theorem injective_of_isLocalDiffeomorphAt_ofFn {k : ℕ∞ω}
    (h : letI := symChartedSpace (K := ℂ) (α := α) (n := n)
      IsLocalDiffeomorphAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) k Sym.ofFn
        p) :
    Injective p := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  have : PerfectSpace α := ChartedSpace.perfectSpace (H := ℂ)
  intro i j hp
  by_contra hij
  -- near `p` the local inverse recovers each tuple from its image
  have hinv := h.localInverse_eventuallyEq_left
  obtain ⟨w, ⟨hw, hne⟩, h₁, h₂⟩ :=
    ((frequently_ofFn_eq_ofFn_and_ne hij hp).and_eventually (hinv.prod_nhds hinv)).exists
  exact hne (h₁.symm.trans ((congrArg h.localInverse hw).trans h₂))

variable [IsManifold 𝓘(ℂ) 1 α]

/-- **The quotient map onto the symmetric power is a local biholomorphism exactly off the
diagonal.** For a Hausdorff complex curve `α` and every regularity `k`, including `ω`, the map
`Sym.ofFn : αⁿ → Sym α n` is a `C^k` local diffeomorphism at a tuple `p` exactly when the points
of `p` are pairwise distinct. -/
theorem isLocalDiffeomorphAt_ofFn_iff (k : ℕ∞ω) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    IsLocalDiffeomorphAt (ModelWithCorners.pi fun _ : Fin n => 𝓘(ℂ)) 𝓘(ℂ, Fin n → ℂ) k Sym.ofFn
      p ↔ Injective p :=
  ⟨injective_of_isLocalDiffeomorphAt_ofFn, fun hp => isLocalDiffeomorphAt_ofFn hp k⟩

end Diagonal

end Sym
