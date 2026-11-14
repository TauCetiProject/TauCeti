/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Orders.Basic
public import TauCeti.Combinatorics.PermutationTriple.Regular

/-!
# The mirror involution of permutation triples

Reflecting the Riemann sphere in its real axis fixes the three branch points `0`, `1` and `∞` and
reverses the orientation of peripheral loops around them. On a permutation triple
`t = (σ0, σ1, σinf)` satisfying `σinf * σ1 * σ0 = 1`, this orientation-reversing involution sends
`t` to

`t.mirror = (σ1 * σ0⁻¹ * σ1⁻¹, σ1⁻¹, σinf⁻¹)`,

conjugating `σ0⁻¹` by `σ1` so that the product relation
`σinf⁻¹ * σ1⁻¹ * (σ1 * σ0⁻¹ * σ1⁻¹) = (σ1 * σ0 * σinf)⁻¹ = 1` continues to hold.

This is the combinatorial counterpart of `TauCeti.TriangleGroup.mirror`, which sends the triangle
group generators `x, y, z` to `y * x⁻¹ * y⁻¹`, `y⁻¹` and `z⁻¹`, and of conjugation by
`J = diag(-1, 1)` on subgroups of `PSL(2, ℤ)`. Unlike the six holomorphic branch-point
reorderings in `TauCeti.Combinatorics.PermutationTriple.BranchPoints`, `mirror` is an involution on
the nose (`TauCeti.PermutationTriple.mirror_mirror`), not only up to relabeling.

## Main definitions

* `TauCeti.PermutationTriple.mirror`: the mirror triple `(σ1 * σ0⁻¹ * σ1⁻¹, σ1⁻¹, σinf⁻¹)`.
* `TauCeti.PermutationTriple.mirrorEquiv`: `mirror` bundled as a self-equivalence of
  `PermutationTriple n`.

## Main results

* `TauCeti.PermutationTriple.mirror_mirror`: `mirror` is an involution.
* `TauCeti.PermutationTriple.mirror_σ1_of_sq_eq_one`: when `t.σ1 ^ 2 = 1`, the second component of
  `t.mirror` agrees with `t.σ1`.
* `TauCeti.PermutationTriple.mirror_smul` and
  `TauCeti.PermutationTriple.mirror_equivalent_mirror_iff`: `mirror` commutes with sheet
  relabeling and preserves isomorphism of triples.
* `TauCeti.PermutationTriple.monodromyGroup_mirror`,
  `TauCeti.PermutationTriple.isConnected_mirror_iff`,
  `TauCeti.PermutationTriple.automorphismGroup_mirror`,
  `TauCeti.PermutationTriple.isRegular_mirror_iff`,
  `TauCeti.PermutationTriple.cycleData_mirror`,
  `TauCeti.PermutationTriple.eulerChar_mirror`,
  `TauCeti.PermutationTriple.genus_mirror`,
  `TauCeti.PermutationTriple.orderTriple_mirror`, and
  `TauCeti.PermutationTriple.hasDividingOrders_mirror_iff`: `mirror` preserves the monodromy group,
  connectedness, the automorphism group, regularity, cycle data, Euler characteristic, genus, and
  component orders.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.5.
* G. A. Jones, D. Singerman, *Belyi functions, hypermaps and Galois groups*, Bull. London Math.
  Soc. 28 (1996), 561–590.
-/

open Equiv

public section

namespace TauCeti.PermutationTriple

variable {n a b c : ℕ}

/-- The mirror of a permutation triple `t = (σ0, σ1, σinf)`: the orientation-reversing involution
sending `t` to `(σ1 * σ0⁻¹ * σ1⁻¹, σ1⁻¹, σinf⁻¹)`. -/
def mirror (t : PermutationTriple n) : PermutationTriple n where
  σ0 := t.σ1 * t.σ0⁻¹ * t.σ1⁻¹
  σ1 := t.σ1⁻¹
  σinf := t.σinf⁻¹
  product_eq_one := by rw [t.σinf_eq_inv]; group

/-- The `0`-component of `t.mirror` is `t.σ1 * t.σ0⁻¹ * t.σ1⁻¹`. -/
@[simp]
theorem mirror_σ0 (t : PermutationTriple n) : t.mirror.σ0 = t.σ1 * t.σ0⁻¹ * t.σ1⁻¹ := (rfl)

/-- The `1`-component of `t.mirror` is `t.σ1⁻¹`. -/
@[simp]
theorem mirror_σ1 (t : PermutationTriple n) : t.mirror.σ1 = t.σ1⁻¹ := (rfl)

/-- The `∞`-component of `t.mirror` is `t.σinf⁻¹`. -/
@[simp]
theorem mirror_σinf (t : PermutationTriple n) : t.mirror.σinf = t.σinf⁻¹ := (rfl)

/-- When `t.σ1` is an involution, the second component of `t.mirror` agrees with `t.σ1`. -/
theorem mirror_σ1_of_sq_eq_one {t : PermutationTriple n} (h : t.σ1 ^ 2 = 1) :
    t.mirror.σ1 = t.σ1 :=
  inv_eq_of_mul_eq_one_right (by rwa [← sq])

/-- Taking the mirror of a permutation triple twice recovers the original triple. -/
@[simp]
theorem mirror_mirror (t : PermutationTriple n) : t.mirror.mirror = t := by
  ext1 <;> simp [mul_assoc]

/-- The mirror involution as an equivalence of `PermutationTriple n` with itself. -/
def mirrorEquiv (n : ℕ) : PermutationTriple n ≃ PermutationTriple n where
  toFun := mirror
  invFun := mirror
  left_inv := mirror_mirror
  right_inv := mirror_mirror

/-- `mirrorEquiv` acts as `PermutationTriple.mirror`. -/
@[simp]
theorem mirrorEquiv_apply (t : PermutationTriple n) : mirrorEquiv n t = t.mirror := (rfl)

/-- `mirrorEquiv` is its own inverse. -/
@[simp]
theorem mirrorEquiv_symm : (mirrorEquiv n).symm = mirrorEquiv n := (rfl)

/-- The mirror of the trivial triple is the trivial triple. -/
@[simp]
theorem mirror_one : (1 : PermutationTriple n).mirror = 1 := by
  ext1 <;> simp

/-- Sheet relabeling commutes with taking the mirror triple. -/
@[simp]
theorem mirror_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    (τ • t).mirror = τ • t.mirror := by
  ext1 <;> simp [mul_assoc]

/-- Isomorphic triples have isomorphic mirrors. -/
theorem Equivalent.mirror {t t' : PermutationTriple n} (h : t.Equivalent t') :
    t.mirror.Equivalent t'.mirror := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact equivalent_iff_exists_smul_eq.mpr ⟨τ, (mirror_smul τ t).symm⟩

/-- Two triples have isomorphic mirrors if and only if they are isomorphic. -/
@[simp]
theorem mirror_equivalent_mirror_iff {t t' : PermutationTriple n} :
    t.mirror.Equivalent t'.mirror ↔ t.Equivalent t' :=
  ⟨fun h ↦ by simpa using h.mirror, Equivalent.mirror⟩

/-- A triple and its mirror generate the same monodromy group. -/
@[simp]
theorem monodromyGroup_mirror (t : PermutationTriple n) :
    t.mirror.monodromyGroup = t.monodromyGroup := by
  refine le_antisymm ?_ ?_
  · rw [← closure_pair_eq_monodromyGroup, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact mul_mem (mul_mem t.σ1_mem_monodromyGroup (inv_mem t.σ0_mem_monodromyGroup))
        (inv_mem t.σ1_mem_monodromyGroup)
    · exact inv_mem t.σ1_mem_monodromyGroup
  · rw [← closure_pair_eq_monodromyGroup, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · have hmem : t.mirror.σ1 * t.mirror.σ0 * t.mirror.σ1⁻¹ ∈ t.mirror.monodromyGroup :=
        mul_mem (mul_mem t.mirror.σ1_mem_monodromyGroup t.mirror.σ0_mem_monodromyGroup)
          (inv_mem t.mirror.σ1_mem_monodromyGroup)
      have heq : (t.mirror.σ1 * t.mirror.σ0 * t.mirror.σ1⁻¹)⁻¹ = t.σ0 := by simp [mul_assoc]
      exact heq ▸ inv_mem hmem
    · simpa using inv_mem t.mirror.σ1_mem_monodromyGroup

/-- The mirror of a triple is connected if and only if the triple is connected. -/
@[simp]
theorem isConnected_mirror_iff (t : PermutationTriple n) :
    t.mirror.IsConnected ↔ t.IsConnected := by
  rw [isConnected_iff, isConnected_iff, monodromyGroup_mirror]

/-- A triple and its mirror have the same automorphism group. -/
@[simp]
theorem automorphismGroup_mirror (t : PermutationTriple n) :
    t.mirror.automorphismGroup = t.automorphismGroup := by
  rw [automorphismGroup_eq_centralizer_monodromyGroup,
    automorphismGroup_eq_centralizer_monodromyGroup, monodromyGroup_mirror]

/-- The mirror of a triple is regular if and only if the triple is regular. -/
@[simp]
theorem isRegular_mirror_iff (t : PermutationTriple n) :
    t.mirror.IsRegular ↔ t.IsRegular := by
  rw [isRegular_iff_card_monodromyGroup, isRegular_iff_card_monodromyGroup,
    isConnected_mirror_iff, monodromyGroup_mirror]

/-- Taking the mirror preserves the ordered full cycle partitions of a triple. -/
@[simp]
theorem cycleData_mirror (t : PermutationTriple n) :
    t.mirror.cycleData = t.cycleData := by
  simp [Prod.ext_iff]

/-- Taking the mirror preserves the ordered cycle counts of a triple. -/
@[simp]
theorem cycleCounts_mirror (t : PermutationTriple n) :
    t.mirror.cycleCounts = t.cycleCounts := by
  rw [cycleCounts_eq_card_cycleData, cycleCounts_eq_card_cycleData, cycleData_mirror]

/-- Taking the mirror preserves the Euler characteristic of a triple. -/
@[simp]
theorem eulerChar_mirror (t : PermutationTriple n) :
    t.mirror.eulerChar = t.eulerChar := by
  simp [eulerChar_def, orbitCount_conj]

/-- Taking the mirror preserves the genus of a triple. -/
@[simp]
theorem genus_mirror (t : PermutationTriple n) :
    t.mirror.genus = t.genus := by
  rw [genus_def, genus_def, eulerChar_mirror]

/-- Taking the mirror preserves the exact component orders of a triple. -/
@[simp]
theorem orderTriple_mirror (t : PermutationTriple n) :
    t.mirror.orderTriple = t.orderTriple := by
  ext : 1
  · simp only [orderTriple_σ0, mirror_σ0]
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv]
  · ext <;> simp

/-- Taking the mirror preserves dividing component orders. -/
theorem hasDividingOrders_mirror_iff (t : PermutationTriple n) :
    t.mirror.HasDividingOrders a b c ↔ t.HasDividingOrders a b c := by
  rw [hasDividingOrders_iff_orderTriple_dvd, hasDividingOrders_iff_orderTriple_dvd,
    orderTriple_mirror]

end TauCeti.PermutationTriple
