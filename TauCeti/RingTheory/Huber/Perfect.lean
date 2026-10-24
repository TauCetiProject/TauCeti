/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import TauCeti.RingTheory.Huber.Uniform
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.RingTheory.Huber.ZeroSequenceOfUnits
import TauCeti.Topology.Algebra.OpenMapping.Henkel

/-!
# Perfect complete Tate rings of characteristic `p`

Let `R` be a complete Hausdorff Tate ring of characteristic `p` which is perfect, so that
Frobenius `φ : R → R`, `x ↦ x ^ p`, is a bijective ring endomorphism. Frobenius is continuous;
by the open mapping theorem it is also open, so its inverse is continuous too. Openness bounds
`p`-th roots: if `R₀` is a ring of definition and `ϖ ∈ R₀` a pseudouniformiser, then for some
`c` every `x` with `x ^ p ∈ ϖ ^ c R₀` lies in `R₀`. Iterating this bounds `R°`, so `R` is
uniform. This is the uniformity half of the statement that, in characteristic `p`, perfectoid
Tate rings are exactly the perfect complete Tate rings.

## Main results

* `TauCeti.Huber.isOpenMap_frobenius`: Frobenius is an open map.
* `TauCeti.Huber.IsUniform.of_perfectRing`: `R` is uniform.

## Implementation notes

Henkel's open mapping theorem `TauCeti.HasZeroSequenceOfUnits.isOpenMap` is applied to Frobenius
as an `R`-equivariant map `R → R`, with `R` acting on the source by multiplication and on the
target through Frobenius, `a • y = a ^ p * y`. Both actions live on the type `R`, so the target
is taken to be the top additive subgroup `(⊤ : AddSubgroup R)`, a copy of `R` on which `R` has
no action of its own.

## References

* P. Scholze, *Étale cohomology of diamonds*, proof of Proposition 3.5.
* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Remark 3.0.3.
-/

public section

open Filter Topology

namespace TauCeti.Huber

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [IsTateRing R] [CompleteSpace R] [T2Space R]

/-- **Frobenius is open** on a perfect complete Hausdorff Tate ring of characteristic `p`, by the
open mapping theorem. In other words, the inverse `x ↦ x ^ (1 / p)` of Frobenius is continuous. -/
theorem isOpenMap_frobenius (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p] :
    IsOpenMap (frobenius R p) := by
  -- the target of Henkel's theorem: a copy of `R`, acted on by `R` through Frobenius
  let N := (⊤ : AddSubgroup R)
  have hN : IsOpen (N : Set R) := by simp [N]
  let _ : SMul R N := ⟨fun a y ↦ ⟨a ^ p * y, AddSubgroup.mem_top _⟩⟩
  have hsmul (a : R) (y : N) : ((a • y : N) : R) = a ^ p * y := rfl
  let _ : DistribMulAction R N :=
    { one_smul y := Subtype.ext (by rw [hsmul, one_pow, one_mul])
      mul_smul a b y := Subtype.ext (by rw [hsmul, hsmul, hsmul, mul_pow, mul_assoc])
      smul_zero a := Subtype.ext (by rw [hsmul, AddSubgroup.coe_zero, mul_zero])
      smul_add a y z := Subtype.ext (by rw [hsmul, AddSubgroup.coe_add, AddSubgroup.coe_add,
        hsmul, hsmul, mul_add]) }
  have : ContinuousConstSMul R N :=
    ⟨fun a ↦ (continuous_const.mul continuous_subtype_val).subtype_mk _⟩
  have : (uniformity R).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace N := hN.baireSpace
  -- Frobenius as an `R`-equivariant additive map `R → N`
  let f : R →+[R] N :=
    { toFun x := ⟨x ^ p, AddSubgroup.mem_top _⟩
      map_smul' a x := Subtype.ext (by simp [hsmul, mul_pow])
      map_zero' := Subtype.ext (zero_pow (Fact.out : p.Prime).ne_zero)
      map_add' x y := Subtype.ext (add_pow_char x y p) }
  have hf : IsOpenMap f := HasZeroSequenceOfUnits.isOpenMap f
    (fun y ↦ (surjective_frobenius R p y).imp fun x hx ↦ Subtype.ext hx)
    ((continuous_pow p).subtype_mk _).continuousAt
    fun x ↦ (continuous_id.mul continuous_const).continuousAt
  -- `f` is `x ↦ x ^ p` by construction, so Frobenius is `f` followed by the inclusion `N → R`
  have hfx (x : R) : (f x : R) = x ^ p := rfl
  have hφ : ⇑(frobenius R p) = Subtype.val ∘ ⇑f :=
    funext fun x ↦ by rw [Function.comp_apply, hfx, frobenius_def]
  rw [hφ]
  exact hN.isOpenMap_subtype_val.comp hf

/-- **A perfect complete Hausdorff Tate ring of characteristic `p` is uniform** (Scholze, *Étale
cohomology of diamonds*, proof of Proposition 3.5): its power-bounded subring `R°` is bounded. -/
theorem IsUniform.of_perfectRing (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p] :
    IsUniform R := by
  obtain ⟨ϖ₀, hϖ₀⟩ := IsTateRing.exists_isPseudoUniformizer (A := R)
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  set R₀ := P.ringOfDefinition
  have hR₀ : (R₀ : Set R) ∈ 𝓝 0 := P.isOpen_ringOfDefinition.mem_nhds R₀.zero_mem
  have hb : IsBounded (R₀ : Set R) := P.isBounded_ringOfDefinition
  -- a pseudouniformiser `ϖ` lying in `R₀`
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hϖ₀.isTopologicallyNilpotent.eventually_mem hR₀)
  set ϖ := ϖ₀ ^ (N + 1)
  have hϖR₀ : ϖ ∈ R₀ := hN _ N.le_succ
  have hϖ : IsTopologicallyNilpotent ϖ := hϖ₀.isTopologicallyNilpotent.pow N.succ_ne_zero
  have hϖu : IsUnit ϖ := hϖ₀.isUnit.pow _
  -- openness of Frobenius: `ϖ ^ c R₀` consists of `p`-th powers of elements of `R₀`
  have hφ := (isOpenMap_frobenius (R := R) p).image_mem_nhds hR₀
  rw [map_zero] at hφ
  obtain ⟨c, hc⟩ := hb.exists_pow_mul_subset hϖ hφ
  have hroot (x : R) (hx : ϖ ^ c * x ^ p ∈ R₀) : ϖ ^ c * x ∈ R₀ := by
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    obtain ⟨y, hy, hyx⟩ := hc (Set.mul_mem_mul (Set.mem_singleton _)
      (R₀.mul_mem (R₀.pow_mem hϖR₀ (c * (p - 2))) hx))
    suffices y = ϖ ^ c * x from this ▸ hy
    refine injective_frobenius R p ?_
    rw [hyx, frobenius_def, mul_pow, ← pow_mul]
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
    rw [Nat.add_sub_cancel_left]
    ring
  -- by induction, `x ^ (p ^ n) ∈ R₀` forces `ϖ ^ c * x ∈ R₀`
  have hiter (n : ℕ) : ∀ x : R, x ^ p ^ n ∈ R₀ → ϖ ^ c * x ∈ R₀ := by
    induction n with
    | zero => exact fun x hx ↦ R₀.mul_mem (R₀.pow_mem hϖR₀ c) (by simpa using hx)
    | succ n ih =>
      refine fun x hx ↦ hroot x (ih (x ^ p) ?_)
      rwa [← pow_mul, ← pow_succ']
  -- hence `R° ⊆ ϖ ^ (-(c + 1)) R₀`
  refine isUniform_iff.mpr (((isBounded_singleton (hϖu.unit⁻¹ ^ (c + 1) : Rˣ).1).mul hb).subset
    fun x hx ↦ ?_)
  obtain ⟨k, hk⟩ := (isPowerBounded_iff.mp hx).exists_pow_mul_subset hϖ hR₀
  have hlt : k ≤ p ^ k := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hpow : (ϖ * x) ^ p ^ k = ϖ ^ (p ^ k - k) * (ϖ ^ k * x ^ p ^ k) := by
    rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt]
  have hy : ϖ ^ c * (ϖ * x) ∈ R₀ := hiter k _ (hpow ▸ R₀.mul_mem (R₀.pow_mem hϖR₀ _)
    (hk (Set.mul_mem_mul rfl ⟨p ^ k, rfl⟩)))
  refine Set.mem_mul.mpr ⟨_, rfl, _, hy, ?_⟩
  calc ((hϖu.unit⁻¹ ^ (c + 1) : Rˣ) : R) * (ϖ ^ c * (ϖ * x))
      = ((hϖu.unit⁻¹ : Rˣ) * ϖ) ^ (c + 1) * x := by rw [Units.val_pow_eq_pow_val]; ring
    _ = x := by rw [hϖu.val_inv_mul, one_pow, one_mul]

end TauCeti.Huber
