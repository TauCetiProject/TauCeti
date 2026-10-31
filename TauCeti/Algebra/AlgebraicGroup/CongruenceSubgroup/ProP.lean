/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CongruenceSubgroup.Topology
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# The first congruence subgroup is pro-`p`

Let `H` be a Hopf algebra over `k` and `R` a commutative `k`-algebra with an ideal `I` containing
the image of a natural number `p`. For `n ≥ 1`, the `p`-th power of a point of the congruence
subgroup `G(R)_{I ^ n}` lies in `G(R)_{I ^ (n + 1)}`. Indeed a point `x ≡ 1 mod I ^ n` is
`1 + D` in the convolution algebra of linear maps `H → R`, with `D` taking values in `I ^ n`, and
in the binomial expansion of `(1 + D) ^ p` the linear term `p • D` takes values in `I ^ (n + 1)`
because `p ∈ I`, while the higher terms take values in `I ^ (2 * n) ≤ I ^ (n + 1)`.

Hence the successive quotients `G(R)_{I ^ n} / G(R)_{I ^ (n + 1)}`, `n ≥ 1`, are killed by `p`.
When the topology of `R` is `I`-adic and `H` is of finite type, the congruence subgroups of the
levels `I ^ n` form a basis of neighbourhoods of the identity, so every open normal subgroup of
`G(R)_I` contains some `G(R)_{I ^ n}`, and `G(R)_I` is pro-`p`. For `𝒢` an affine group of finite
type over the valuation ring `O` of a nonarchimedean local field with residue characteristic `p`,
this says that the first congruence subgroup `𝒢(O)₁` is pro-`p`. The level must be a proper
ideal: `𝒢(O)` itself need not be pro-`p`, since for `GL₂` its quotient by `𝒢(O)₁` is `GL₂` of the
residue field, whose order is not a power of `p`.

## Main results

* `TauCeti.HopfAlgebra.pow_mem_congruenceSubgroup_pow_succ`: for `n ≠ 0` and `(p : R) ∈ I`,
  `x ∈ G(R)_{I ^ n}` implies `x ^ p ∈ G(R)_{I ^ (n + 1)}`.
* `TauCeti.HopfAlgebra.pow_pow_mem_congruenceSubgroup_pow_succ`: iterating, `x ∈ G(R)_I` implies
  `x ^ (p ^ n) ∈ G(R)_{I ^ (n + 1)}`.
* `TauCeti.HopfAlgebra.isProP_congruenceSubgroup`: for an `I`-adic topology and `H` of finite
  type, `G(R)_I` is pro-`p`.
* `TauCeti.HopfAlgebra.isProP_congruenceSubgroup_maximalIdeal`: over a compact Hausdorff
  noetherian local ring whose residue field has characteristic `p`, the first congruence subgroup
  is pro-`p`.

## References

* V. Platonov, A. Rapinchuk, I. Rapinchuk, *Algebraic groups and number theory*, vol. 1,
  2nd ed. (2023), §3.1, p. 126, and Lemma 3.38, p. 160.
* J. S. Milne, *Algebraic Groups*, Cambridge Stud. Adv. Math. 170 (2017), 12.5, pp. 184–185.
-/

public section

open Coalgebra WithConv Topology

namespace TauCeti

namespace HopfAlgebra

variable {k H R : Type*} [CommSemiring k] [Semiring H] [_root_.HopfAlgebra k H]
  [CommRing R] [Algebra k R]

/-- **Congruence quotients are killed by `p`.** If `(p : R) ∈ I` and `n ≠ 0`, the `p`-th power of
a point of the congruence subgroup of level `I ^ n` lies in the congruence subgroup of level
`I ^ (n + 1)`. -/
theorem pow_mem_congruenceSubgroup_pow_succ {I : Ideal R} {p n : ℕ} (hp : (p : R) ∈ I)
    (hn : n ≠ 0) {x : WithConv (H →ₐ[k] R)} (hx : x ∈ congruenceSubgroup k H (I ^ n)) :
    x ^ p ∈ congruenceSubgroup k H (I ^ (n + 1)) := by
  -- Write `x = 1 + D` in the convolution algebra of linear maps, with `D` valued in `I ^ n`.
  set D : WithConv (H →ₗ[k] R) := toConv x.ofConv.toLinearMap - 1 with hD_def
  have hD : ∀ h, D h ∈ I ^ n := fun h ↦ by
    simpa [hD_def] using mem_congruenceSubgroup_iff.1 hx h
  -- Each term `choose p (m + 1) • D ^ (m + 1)` of `(1 + D) ^ p - 1` is valued in `I ^ (n + 1)`.
  have hterm : ∀ m h, (p.choose (m + 1) • D ^ (m + 1)) h ∈ I ^ (n + 1) := by
    intro m h
    rw [ofConv_smul, LinearMap.smul_apply]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.choose_one_right, zero_add, pow_one, nsmul_eq_mul, pow_succ']
      exact Ideal.mul_mem_mul hp (hD h)
    · have hle : I ^ (n * (m + 1)) ≤ I ^ (n + 1) :=
        Ideal.pow_le_pow_right (by have := Nat.pos_of_ne_zero hn; nlinarith)
      exact Submodule.smul_of_tower_mem _ _
        (hle (pow_mul I n (m + 1) ▸ LinearMap.convPow_apply_mem_pow hD (m + 1) h))
  have hpow : toConv (x ^ p).ofConv.toLinearMap - 1 =
      ∑ m ∈ Finset.range p, p.choose (m + 1) • D ^ (m + 1) := by
    rw [AlgHom.toLinearMap_convPow, show toConv x.ofConv.toLinearMap = D + 1 by simp [hD_def],
      (Commute.one_right D).add_pow, Finset.sum_range_succ']
    simp only [one_pow, mul_one, Nat.sub_zero, Nat.choose_zero_right, pow_zero, Nat.cast_one,
      add_sub_cancel_right, nsmul_eq_mul, Nat.cast_comm]
  refine mem_congruenceSubgroup_iff.2 fun h ↦ ?_
  have hval := congrArg (fun f : WithConv (H →ₗ[k] R) ↦ f h) hpow
  simp only [ofConv_sub, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    LinearMap.convOne_apply, ofConv_sum, LinearMap.sum_apply] at hval
  rw [hval]
  exact Ideal.sum_mem _ fun m _ ↦ hterm m h

/-- Iterating `pow_mem_congruenceSubgroup_pow_succ`: if `(p : R) ∈ I`, the `p ^ n`-th power of a
point of the congruence subgroup of level `I` lies in the congruence subgroup of level
`I ^ (n + 1)`. -/
theorem pow_pow_mem_congruenceSubgroup_pow_succ {I : Ideal R} {p : ℕ} (hp : (p : R) ∈ I)
    {x : WithConv (H →ₐ[k] R)} (hx : x ∈ congruenceSubgroup k H I) (n : ℕ) :
    x ^ p ^ n ∈ congruenceSubgroup k H (I ^ (n + 1)) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa [pow_succ, pow_mul] using pow_mem_congruenceSubgroup_pow_succ hp n.succ_ne_zero ih

/-- **The first congruence subgroup is pro-`p`.** If the topology of `R` is `I`-adic, `(p : R) ∈ I`
and `H` is of finite type over `k`, then the congruence subgroup of level `I`, with its subspace
topology, is pro-`p`: each of its quotients by an open normal subgroup is a `p`-group. -/
theorem isProP_congruenceSubgroup [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra.FiniteType k H] {I : Ideal R} (hI : IsAdic I) {p : ℕ} (hp : (p : R) ∈ I) :
    IsProP p (congruenceSubgroup k H I) := by
  refine isProP_iff.2 fun U ↦ ?_
  -- `U` is a neighbourhood of `1` in `G(R)_I`, so it contains the trace of some `G(R)_{I ^ n}`.
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1 (U.isOpen.mem_nhds U.one_mem')
  obtain ⟨n, -, hn⟩ := (hasBasis_nhds_one_congruenceSubgroup_pow (k := k) (H := H) hI).mem_iff.1 hV
  refine fun g ↦ QuotientGroup.induction_on g fun x ↦ ⟨n, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  refine hVU (hn ?_)
  exact congruenceSubgroup_mono k H R (Ideal.pow_le_pow_right n.le_succ)
    (pow_pow_mem_congruenceSubgroup_pow_succ hp x.2 n)

variable (k H R) in
/-- Over a compact Hausdorff noetherian local ring `R` whose residue field has characteristic `p`,
for instance the valuation ring `O` of a nonarchimedean local field with residue characteristic
`p`, the first congruence subgroup `𝒢(O)₁` of an affine group of finite type is pro-`p`. -/
theorem isProP_congruenceSubgroup_maximalIdeal [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R] [Algebra.FiniteType k H]
    (p : ℕ) [CharP (IsLocalRing.ResidueField R) p] :
    IsProP p (congruenceSubgroup k H (IsLocalRing.maximalIdeal R)) :=
  isProP_congruenceSubgroup (IsLocalRing.isAdic_maximalIdeal R) <| by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]

end HopfAlgebra

end TauCeti
