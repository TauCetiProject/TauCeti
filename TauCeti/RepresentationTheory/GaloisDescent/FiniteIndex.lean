/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Galois descent from a subgroup of finite index

Let a group `G` act on a field `F` by multiplicative maps (for instance by field automorphisms),
let `j : Γ →* G` be a homomorphism and let `U ≤ G` be a subgroup that is the fixer of its own
fixed points `F^U`. Let `τ` be a representation of `Γ` on an `F`-vector space `V` that is
semilinear along `j`, that is `τ g (a • v) = (j g • a) • τ g v`. If `j⁻¹(U)` has finite index in
`Γ` (for instance if `U` has finite index in `G`), every vector of `V` fixed by `j⁻¹(U)` lies in
the `F`-span of the vectors fixed by all of `Γ`.

The group `G` need not be finite, a Galois group or a topological group, the action of `G` on
`F` need not be faithful, and `j` need not be injective or surjective. The case `U = ⊥`, `j = id`,
with `G` finite and acting faithfully, is `TauCeti.GaloisDescent.span_invariants_eq_top`.

## Main results

* `TauCeti.GaloisDescent.mem_span_invariants_of_finiteIndex`: a vector fixed by `j⁻¹(U)` lies in
  the `F`-span of the `Γ`-invariant vectors.

## Proof

For `a ∈ F^U`, the sum of `τ g (a • y)` over representatives `g` of the cosets `Γ ⧸ j⁻¹(U)` is
`Γ`-invariant. The cosets act on `F^U` by pairwise distinct monoid homomorphisms
`a ↦ j g • a`, which are linearly independent over `F` (Dedekind); a linear form vanishing on the
invariant vectors therefore vanishes on `y`.

## References

* A. Speiser, *Zahlentheoretische Sätze aus der Gruppentheorie*, Mathematische Zeitschrift 5
  (1919), 1–6.
* J.-P. Serre, *Galois Cohomology*, Springer (1997).
* A related statement is `New.Period.mem_span_fixed` in the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (`Lib/ClassField/GaloisCohomology/KummerCyclicClasses`).
-/

public section

namespace TauCeti.GaloisDescent

variable {k Γ G F V : Type*} [CommRing k] [Group Γ] [Group G] [Field F]
variable [MulDistribMulAction G F] [AddCommGroup V] [Module k V] [Module F V]

/-- Two representatives of the same coset of `j⁻¹(U)` act alike on `a • y`, for `a` fixed by `U`
and `y` fixed by `j⁻¹(U)`. -/
private theorem apply_smul_eq_of_mk_eq {j : Γ →* G} {U : Subgroup G} {τ : Representation k Γ V}
    (hτ : ∀ (g : Γ) (a : F) (v : V), τ g (a • v) = (j g • a) • τ g v) {y : V}
    (hy : ∀ g, j g ∈ U → τ g y = y) {a : F} (ha : a ∈ MulAction.fixedPoints U F) {g₁ g₂ : Γ}
    (h : (g₁ : Γ ⧸ U.comap j) = g₂) : τ g₁ (a • y) = τ g₂ (a • y) := by
  have hmem : j (g₁⁻¹ * g₂) ∈ U := Subgroup.mem_comap.mp (QuotientGroup.eq.mp h)
  have hfix : j (g₁⁻¹ * g₂) • a = a := by
    simpa only [Subgroup.smul_def] using ha ⟨_, hmem⟩
  calc τ g₁ (a • y)
      _ = τ g₁ (τ (g₁⁻¹ * g₂) (a • y)) := by rw [hτ (g₁⁻¹ * g₂), hfix, hy _ hmem]
      _ = τ g₂ (a • y) := by rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]

/-- **Galois descent from a subgroup of finite index.** Let a group `G` act on the field `F` by
multiplicative maps, let `j : Γ →* G` be a homomorphism and `U ≤ G` a subgroup containing every
element that fixes `F^U` pointwise, with `j⁻¹(U)` of finite index in `Γ` (which holds when `U` has
finite index in `G`). If the representation `τ` of `Γ` on the `F`-vector space `V` is semilinear
along `j`, then every vector fixed by all `g` with `j g ∈ U` lies in the `F`-span of the
`Γ`-invariant vectors. -/
theorem mem_span_invariants_of_finiteIndex (j : Γ →* G) (U : Subgroup G)
    [(U.comap j).FiniteIndex] (hU : fixingSubgroup G (MulAction.fixedPoints U F) ≤ U)
    {τ : Representation k Γ V} (hτ : ∀ (g : Γ) (a : F) (v : V), τ g (a • v) = (j g • a) • τ g v)
    {y : V} (hy : ∀ g, j g ∈ U → τ g y = y) :
    y ∈ Submodule.span F (τ.invariants : Set V) := by
  classical
  let := Fintype.ofFinite (Γ ⧸ U.comap j)
  let K := FixedPoints.submonoid U F
  by_contra hy'
  obtain ⟨f, hfy, hker⟩ := Submodule.exists_le_ker_of_notMem hy'
  -- The coset sums `∑ q, τ q.out (a • y)` are invariant vectors.
  have hT (a : K) : ∑ q : Γ ⧸ U.comap j, τ q.out ((a : F) • y) ∈ τ.invariants := by
    rw [Representation.mem_invariants]
    intro g
    rw [map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q ↦ ?_
    rw [← mul_apply_eq_comp, ← map_mul]
    refine apply_smul_eq_of_mk_eq hτ hy a.property ?_
    -- Left multiplication by `g` is compatible with the projection to `Γ ⧸ j⁻¹(U)`.
    simp [← smul_eq_mul, ← MulAction.Quotient.smul_mk]
  -- The coset representatives act on `F^U` by pairwise distinct monoid homomorphisms.
  let σ : Γ ⧸ U.comap j → (K →* F) := fun q ↦
    (MulDistribMulAction.toMonoidHom F (j q.out)).comp K.subtype
  have hσ_apply (q : Γ ⧸ U.comap j) (a : K) : σ q a = j q.out • (a : F) := by
    simp only [σ, MonoidHom.comp_apply, MulDistribMulAction.toMonoidHom_apply,
      Submonoid.coe_subtype]
  have hσ : Function.Injective σ := by
    intro q₁ q₂ hq
    rw [← q₁.out_eq', ← q₂.out_eq', QuotientGroup.eq, Subgroup.mem_comap]
    refine hU ((mem_fixingSubgroup_iff G).mpr fun a ha ↦ ?_)
    have h : j q₁.out • a = j q₂.out • a := by
      simpa only [hσ_apply] using DFunLike.congr_fun hq ⟨a, ha⟩
    simp [mul_smul, ← h]
  have hli := (linearIndependent_monoidHom K F).comp σ hσ
  have hsum : ∑ q : Γ ⧸ U.comap j, f (τ q.out y) • ⇑(σ q) = 0 := by
    ext a
    -- `f` vanishes on the invariant vector `∑ q, τ q.out (a • y)`.
    have hz : ∑ q : Γ ⧸ U.comap j, (j q.out • (a : F)) * f (τ q.out y) = 0 := by
      simpa only [map_sum, hτ, map_smul, smul_eq_mul] using
        LinearMap.mem_ker.mp (hker (Submodule.subset_span (hT a)))
    rw [Finset.sum_apply, Pi.zero_apply, ← hz]
    exact Finset.sum_congr rfl fun q _ ↦ by rw [Pi.smul_apply, hσ_apply, smul_eq_mul, mul_comm]
  have h1 := Fintype.linearIndependent_iff.mp hli _ hsum (QuotientGroup.mk 1)
  -- The representative of the trivial coset fixes `y`.
  have hout := apply_smul_eq_of_mk_eq (a := 1) hτ hy (fun _ ↦ smul_one _)
    (QuotientGroup.mk 1 : Γ ⧸ U.comap j).out_eq'
  simp only [one_smul, map_one, one_apply_eq_self] at hout
  exact hfy (hout ▸ h1)

end TauCeti.GaloisDescent
