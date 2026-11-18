/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DiffContOnCl
public import TauCeti.Analysis.Complex.UnitDisc.AdjointBoundary
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Prod

/-!
# The disc problem with a diagonal boundary condition in higher rank

Fix a finite index type `ι` and integers `k : ι → ℤ`. This file treats the Cauchy–Riemann
operator `∂/∂(conj z)` on the closed unit disc for maps to `ι → ℂ`, with the *diagonal* totally
real boundary condition

`u(e^{iθ}) ∈ ⊕ᵢ e^{i kᵢ θ/2} ℝ`,

stated coordinatewise without square roots as `u w i = w ^ k i * conj (u w i)` for `‖w‖ = 1`.
The boundary loop is the direct sum of the rotating lines of
`TauCeti.Analysis.Complex.UnitDisc.RotatingLineBoundary`, so, informally, iterating the direct-sum
axiom `TauCeti.TotallyRealLoop.maslovIndex_prod` gives its Maslov index as `μ = ∑ i, k i`. This
file does not define the boundary loop for a general `ι`; the comparison with the Maslov index is
formalized only in rank two.

The problem decouples: a map solves it exactly when each coordinate solves the rank one problem
for the index `k i`. So the kernel `TauCeti.unitDiscCauchyRiemannKernelPi k` is the product of the
rank one kernels (`TauCeti.unitDiscCauchyRiemannKernelPiEquiv`), and the same holds for the
adjoint kernel `TauCeti.unitDiscAdjointKernelPi k` (`TauCeti.unitDiscAdjointKernelPiEquiv`). The
dimension counts of the rank one problem then give

`dim ker - dim (adjoint ker) = ∑ i, (k i + 1) = n + ∑ i, k i = n χ(D) + μ`

for `n` the cardinality of `ι` and `μ = ∑ i, k i`
(`TauCeti.finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi`), the
Riemann–Roch index formula on the disc once the adjoint kernel is identified with the cokernel.

Two examples illustrate these formulas. For `k = 0`, the disc with boundary condition `(ℂⁿ, ℝⁿ)`,
the kernel is the real constants `ℝⁿ` (`TauCeti.mem_unitDiscCauchyRiemannKernelPi_zero_iff`), of
real dimension `n` (`TauCeti.finrank_unitDiscCauchyRiemannKernelPi_zero`), and the adjoint kernel
vanishes. In rank two, the dimension identity is matched with the Maslov index of the direct sum
of the two rotating real lines
(`TauCeti.finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi_pair`); for
`(ℂ², ℝ ⊕ e^{iθ}ℝ)` the kernel has dimension `1 + 3 = 4 = 2 + μ` with `μ = 0 + 2`
(`TauCeti.finrank_unitDiscCauchyRiemannKernelPi_zero_two`).

## Main definitions

* `TauCeti.unitDiscCauchyRiemannKernelPi k`: the real subspace of maps from the closed unit disc
  to `ι → ℂ` whose `i`-th coordinate lies in `TauCeti.unitDiscCauchyRiemannKernel (k i)`.
* `TauCeti.unitDiscAdjointKernelPi k`: the same for the adjoint kernels
  `TauCeti.unitDiscAdjointKernel (k i)`.
* `TauCeti.unitDiscCauchyRiemannKernelPiEquiv k`, `TauCeti.unitDiscAdjointKernelPiEquiv k`: the
  real-linear isomorphisms with the products of the rank one kernels.

## Main results

* `TauCeti.mem_unitDiscCauchyRiemannKernelPi_iff_exists`,
  `TauCeti.mem_unitDiscAdjointKernelPi_iff_exists`: membership as restrictions of maps
  `ℂ → ι → ℂ` holomorphic on the open disc, continuous on its closure, and satisfying the
  diagonal boundary condition.
* `TauCeti.finrank_unitDiscCauchyRiemannKernelPi`, `TauCeti.finrank_unitDiscAdjointKernelPi`:
  the dimensions `∑ i, (k i + 1).toNat` and `∑ i, (-k i - 1).toNat`.
* `TauCeti.finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi`: the
  dimension identity `n + ∑ i, k i`.
* `TauCeti.unitDiscAdjointKernelPi_eq_bot`: the adjoint kernel vanishes when every `k i ≥ -1`.
* `TauCeti.mem_unitDiscCauchyRiemannKernelPi_zero_iff`,
  `TauCeti.finrank_unitDiscCauchyRiemannKernelPi_zero`: for `k = 0` the kernel is the real
  constants, of dimension `n`.
* `TauCeti.finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi_pair`,
  `TauCeti.finrank_unitDiscCauchyRiemannKernelPi_zero_two`: in rank two the dimension identity
  is `2 + μ` for `μ` the Maslov index of the direct sum of the boundary loops.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the Riemann–Roch theorem, Theorem C.1.10, and
  its proof by splitting a boundary condition into rotating lines; the Maslov index is
  Appendix C.3).
-/

public section

namespace TauCeti

open Complex Metric Module Set
open scoped ComplexConjugate

variable {ι : Type*}

/-! ### The kernel -/

/-- The kernel of the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc for maps to
`ι → ℂ` with the diagonal boundary condition `u(e^{iθ}) ∈ ⊕ᵢ e^{i kᵢ θ/2} ℝ`: the maps `g` from
the closed disc to `ι → ℂ` whose `i`-th coordinate lies in
`TauCeti.unitDiscCauchyRiemannKernel (k i)`. Equivalently, `g` is the restriction of a map
holomorphic on the open disc and continuous on its closure with `u w i = w ^ k i * conj (u w i)`
for `‖w‖ = 1` (`TauCeti.mem_unitDiscCauchyRiemannKernelPi_iff_exists`). -/
def unitDiscCauchyRiemannKernelPi (k : ι → ℤ) :
    Submodule ℝ (closedBall (0 : ℂ) 1 → ι → ℂ) where
  carrier := {g | ∀ i, (fun z => g z i) ∈ unitDiscCauchyRiemannKernel (k i)}
  add_mem' hf hg i := add_mem (hf i) (hg i)
  zero_mem' _ := zero_mem _
  smul_mem' c _ hg i := Submodule.smul_mem _ c (hg i)

variable {k : ι → ℤ} {g : closedBall (0 : ℂ) 1 → ι → ℂ}

/-- A map lies in the diagonal kernel exactly when each coordinate lies in the rank one kernel. -/
@[simp]
theorem mem_unitDiscCauchyRiemannKernelPi_iff :
    g ∈ unitDiscCauchyRiemannKernelPi k ↔
      ∀ i, (fun z => g z i) ∈ unitDiscCauchyRiemannKernel (k i) :=
  Iff.rfl

/-- Membership in the diagonal kernel, unfolded: `g` is the restriction of a map holomorphic on
the open disc and continuous on its closure, satisfying `u w i = w ^ k i * conj (u w i)` on the
unit circle for every `i`. -/
theorem mem_unitDiscCauchyRiemannKernelPi_iff_exists [Fintype ι] :
    g ∈ unitDiscCauchyRiemannKernelPi k ↔ ∃ u : ℂ → ι → ℂ, DiffContOnCl ℂ u (ball 0 1) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, ∀ i, u w i = w ^ k i * conj (u w i)) ∧
      (closedBall 0 1).domRestrict u = g := by
  simp only [mem_unitDiscCauchyRiemannKernelPi_iff, mem_unitDiscCauchyRiemannKernel_iff]
  exact forall_exists_diffContOnCl_iff (fun i w c => c = w ^ k i * conj c) g

/-- **The diagonal kernel splits.** The real-linear isomorphism from the diagonal kernel to the
product of the rank one kernels, taking a map to its coordinates. -/
def unitDiscCauchyRiemannKernelPiEquiv (k : ι → ℤ) :
    unitDiscCauchyRiemannKernelPi k ≃ₗ[ℝ] Π i, unitDiscCauchyRiemannKernel (k i) where
  toFun g i := ⟨fun z => (g : closedBall (0 : ℂ) 1 → ι → ℂ) z i,
    mem_unitDiscCauchyRiemannKernelPi_iff.mp g.2 i⟩
  invFun f := ⟨fun z i => (f i : closedBall (0 : ℂ) 1 → ℂ) z,
    mem_unitDiscCauchyRiemannKernelPi_iff.mpr fun i => (f i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem unitDiscCauchyRiemannKernelPiEquiv_apply (g : unitDiscCauchyRiemannKernelPi k) (i : ι)
    (z : closedBall (0 : ℂ) 1) :
    (unitDiscCauchyRiemannKernelPiEquiv k g i : closedBall (0 : ℂ) 1 → ℂ) z =
      (g : closedBall (0 : ℂ) 1 → ι → ℂ) z i := by
  rfl

@[simp]
theorem unitDiscCauchyRiemannKernelPiEquiv_symm_apply
    (f : Π i, unitDiscCauchyRiemannKernel (k i)) (z : closedBall (0 : ℂ) 1) (i : ι) :
    ((unitDiscCauchyRiemannKernelPiEquiv k).symm f : closedBall (0 : ℂ) 1 → ι → ℂ) z i =
      (f i : closedBall (0 : ℂ) 1 → ℂ) z := by
  rfl

/-- The diagonal kernel is a finite-dimensional real vector space. -/
instance finiteDimensional_unitDiscCauchyRiemannKernelPi [Finite ι] (k : ι → ℤ) :
    FiniteDimensional ℝ (unitDiscCauchyRiemannKernelPi k) :=
  (unitDiscCauchyRiemannKernelPiEquiv k).symm.finiteDimensional

/-- The diagonal kernel has real dimension `∑ i, max (k i + 1) 0`. -/
theorem finrank_unitDiscCauchyRiemannKernelPi [Fintype ι] (k : ι → ℤ) :
    finrank ℝ (unitDiscCauchyRiemannKernelPi k) = ∑ i, (k i + 1).toNat := by
  rw [(unitDiscCauchyRiemannKernelPiEquiv k).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ => finrank_unitDiscCauchyRiemannKernel (k i)

/-- **The disc with boundary condition `(ℂⁿ, ℝⁿ)`.** For real boundary values in every coordinate,
the solutions are exactly the real constants `ℝⁿ`. -/
theorem mem_unitDiscCauchyRiemannKernelPi_zero_iff :
    g ∈ unitDiscCauchyRiemannKernelPi (0 : ι → ℤ) ↔ ∃ r : ι → ℝ, g = fun _ i => (r i : ℂ) := by
  simp only [mem_unitDiscCauchyRiemannKernelPi_iff, Pi.zero_apply,
    mem_unitDiscCauchyRiemannKernel_zero_iff]
  refine ⟨fun h => ?_, ?_⟩
  · choose r hr using h
    exact ⟨r, funext fun z => funext fun i => congrFun (hr i) z⟩
  · rintro ⟨r, rfl⟩ i
    exact ⟨r i, rfl⟩

/-- The disc with boundary condition `(ℂⁿ, ℝⁿ)` has kernel of real dimension `n`. -/
theorem finrank_unitDiscCauchyRiemannKernelPi_zero [Fintype ι] :
    finrank ℝ (unitDiscCauchyRiemannKernelPi (0 : ι → ℤ)) = Fintype.card ι := by
  simp [finrank_unitDiscCauchyRiemannKernelPi]

/-! ### The adjoint kernel -/

/-- The kernel of the adjoint problem for the diagonal boundary condition
`u(e^{iθ}) ∈ ⊕ᵢ e^{i kᵢ θ/2} ℝ`: the maps `g` from the closed disc to `ι → ℂ` whose `i`-th
coordinate lies in the rank one adjoint kernel `TauCeti.unitDiscAdjointKernel (k i)`. -/
def unitDiscAdjointKernelPi (k : ι → ℤ) : Submodule ℝ (closedBall (0 : ℂ) 1 → ι → ℂ) where
  carrier := {g | ∀ i, (fun z => g z i) ∈ unitDiscAdjointKernel (k i)}
  add_mem' hf hg i := add_mem (hf i) (hg i)
  zero_mem' _ := zero_mem _
  smul_mem' c _ hg i := Submodule.smul_mem _ c (hg i)

/-- A map lies in the diagonal adjoint kernel exactly when each coordinate lies in the rank one
adjoint kernel. -/
@[simp]
theorem mem_unitDiscAdjointKernelPi_iff :
    g ∈ unitDiscAdjointKernelPi k ↔ ∀ i, (fun z => g z i) ∈ unitDiscAdjointKernel (k i) :=
  Iff.rfl

/-- Membership in the diagonal adjoint kernel, unfolded: `g` is the restriction of a map
holomorphic on the open disc and continuous on its closure that satisfies the adjoint boundary
condition of `TauCeti.mem_unitDiscAdjointKernel_iff` in every coordinate. -/
theorem mem_unitDiscAdjointKernelPi_iff_exists [Fintype ι] :
    g ∈ unitDiscAdjointKernelPi k ↔ ∃ u : ℂ → ι → ℂ, DiffContOnCl ℂ u (ball 0 1) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, ∀ i,
        -I * conj w * conj (u w i) = w ^ k i * conj (-I * conj w * conj (u w i))) ∧
      (closedBall 0 1).domRestrict u = g := by
  simp only [mem_unitDiscAdjointKernelPi_iff, mem_unitDiscAdjointKernel_iff]
  exact forall_exists_diffContOnCl_iff
    (fun i w c => -I * conj w * conj c = w ^ k i * conj (-I * conj w * conj c)) g

/-- **The diagonal adjoint kernel splits.** The real-linear isomorphism from the diagonal adjoint
kernel to the product of the rank one adjoint kernels, taking a map to its coordinates. -/
def unitDiscAdjointKernelPiEquiv (k : ι → ℤ) :
    unitDiscAdjointKernelPi k ≃ₗ[ℝ] Π i, unitDiscAdjointKernel (k i) where
  toFun g i := ⟨fun z => (g : closedBall (0 : ℂ) 1 → ι → ℂ) z i,
    mem_unitDiscAdjointKernelPi_iff.mp g.2 i⟩
  invFun f := ⟨fun z i => (f i : closedBall (0 : ℂ) 1 → ℂ) z,
    mem_unitDiscAdjointKernelPi_iff.mpr fun i => (f i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem unitDiscAdjointKernelPiEquiv_apply (g : unitDiscAdjointKernelPi k) (i : ι)
    (z : closedBall (0 : ℂ) 1) :
    (unitDiscAdjointKernelPiEquiv k g i : closedBall (0 : ℂ) 1 → ℂ) z =
      (g : closedBall (0 : ℂ) 1 → ι → ℂ) z i := by
  rfl

@[simp]
theorem unitDiscAdjointKernelPiEquiv_symm_apply (f : Π i, unitDiscAdjointKernel (k i))
    (z : closedBall (0 : ℂ) 1) (i : ι) :
    ((unitDiscAdjointKernelPiEquiv k).symm f : closedBall (0 : ℂ) 1 → ι → ℂ) z i =
      (f i : closedBall (0 : ℂ) 1 → ℂ) z := by
  rfl

/-- The diagonal adjoint kernel is a finite-dimensional real vector space. -/
instance finiteDimensional_unitDiscAdjointKernelPi [Finite ι] (k : ι → ℤ) :
    FiniteDimensional ℝ (unitDiscAdjointKernelPi k) :=
  (unitDiscAdjointKernelPiEquiv k).symm.finiteDimensional

/-- The diagonal adjoint kernel has real dimension `∑ i, max (-k i - 1) 0`. -/
theorem finrank_unitDiscAdjointKernelPi [Fintype ι] (k : ι → ℤ) :
    finrank ℝ (unitDiscAdjointKernelPi k) = ∑ i, (-k i - 1).toNat := by
  rw [(unitDiscAdjointKernelPiEquiv k).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun i _ => finrank_unitDiscAdjointKernel (k i)

/-- If every index `k i` is at least `-1`, the diagonal adjoint problem has only the zero
solution. -/
theorem unitDiscAdjointKernelPi_eq_bot (hk : ∀ i, -1 ≤ k i) : unitDiscAdjointKernelPi k = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun g hg => funext fun z => funext fun i => by
    have hgi := hg i
    rw [unitDiscAdjointKernel_eq_bot (hk i), Submodule.mem_bot] at hgi
    exact congrFun hgi z

/-! ### The index -/

/-- **Kernel minus adjoint kernel for the diagonal boundary condition.** The dimension of the
kernel minus the dimension of the adjoint kernel is `n + ∑ i, k i`, for `n` the cardinality of
`ι`. Informally this is `n χ(D) + μ`, with `∑ i, k i` the Maslov index `μ` of the diagonal boundary
loop; the comparison with the Maslov index is formalized in rank two in
`TauCeti.finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi_pair`. Under
the duality identifying the adjoint kernel with the cokernel (not formalized here), this is the
Fredholm index of the Cauchy–Riemann operator. -/
theorem finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi [Fintype ι]
    (k : ι → ℤ) :
    (finrank ℝ (unitDiscCauchyRiemannKernelPi k) : ℤ) - finrank ℝ (unitDiscAdjointKernelPi k) =
      Fintype.card ι + ∑ i, k i := by
  rw [finrank_unitDiscCauchyRiemannKernelPi, finrank_unitDiscAdjointKernelPi, Nat.cast_sum,
    Nat.cast_sum, ← Finset.sum_sub_distrib, Fintype.card_eq_sum_ones, Nat.cast_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by push_cast; omega

/-- **The index in rank two against the Maslov index.** For the boundary condition
`(ℂ², e^{i k₁ θ/2} ℝ ⊕ e^{i k₂ θ/2} ℝ)` on the disc, the dimension of the kernel minus the
dimension of the adjoint kernel is `2 χ(D) + μ`, where `μ` is the Maslov index of the direct sum
of the two rotating real lines, computed by the direct-sum axiom
`TauCeti.TotallyRealLoop.maslovIndex_prod`. -/
theorem finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi_pair
    (k₁ k₂ : ℤ) :
    (finrank ℝ (unitDiscCauchyRiemannKernelPi ![k₁, k₂]) : ℤ) -
        finrank ℝ (unitDiscAdjointKernelPi ![k₁, k₂]) =
      2 + ((TotallyRealLoop.rotationZPow isMaximalTotallyReal_span_one k₁).prod
        (TotallyRealLoop.rotationZPow isMaximalTotallyReal_span_one k₂)).maslovIndex := by
  rw [finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi,
    TotallyRealLoop.maslovIndex_prod, TotallyRealLoop.maslovIndex_rotationZPow,
    TotallyRealLoop.maslovIndex_rotationZPow, Module.finrank_self]
  simp [Fin.sum_univ_two]

/-- **The disc with boundary condition `(ℂ², ℝ ⊕ e^{iθ}ℝ)`.** The kernel has real dimension
`1 + 3 = 4`, which is `2 + μ` for the Maslov index `μ = 0 + 2` of the direct sum of the constant
real line and the full turn of the real line. -/
theorem finrank_unitDiscCauchyRiemannKernelPi_zero_two :
    (finrank ℝ (unitDiscCauchyRiemannKernelPi ![0, 2]) : ℤ) =
      2 + ((TotallyRealLoop.const isMaximalTotallyReal_span_one).prod
        (TotallyRealLoop.rotationZPow isMaximalTotallyReal_span_one 2)).maslovIndex := by
  have h := finrank_unitDiscCauchyRiemannKernelPi_sub_finrank_unitDiscAdjointKernelPi_pair 0 2
  rwa [TotallyRealLoop.rotationZPow_zero,
    unitDiscAdjointKernelPi_eq_bot fun i => by fin_cases i <;> decide, finrank_bot,
    Nat.cast_zero, sub_zero] at h

end TauCeti
