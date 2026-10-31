/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RingTheory.Invariant.Free
import Mathlib.LinearAlgebra.TensorProduct.Lift
import TauCeti.Algebra.Group.Action.MulDistribMulAction
import TauCeti.RepresentationTheory.NormInvariants
import TauCeti.RingTheory.Invariant.Basic

/-!
# Galois descent of modules along a free action of a finite group

Let a finite group `G` act freely on a commutative `A`-algebra `B` by `A`-algebra automorphisms
with ring of invariants `A`; by Chase–Harrison–Rosenberg this says that `B` is a finite étale
`G`-torsor over `A` (`TauCeti.Algebra.isFiniteEtaleTorsor_iff`), up to injectivity of `A → B`.
This file constructs the two comparison isomorphisms of finite Galois descent for modules: every
`B`-module with semilinear `G`-action is the base change of its invariants, and, when `A → B` is
injective, every `A`-module is the invariants of its base change.

A *semilinear* action on a `B`-module `N` is a distributive action of `G` with
`g • (b • n) = (g • b) • (g • n)` (Mathlib's `SMulDistribClass G B N`). Such an action is
`A`-linear (`TauCeti.MulSemiringAction.smulCommClass_of_smulDistribClass`), so its invariants form
the `A`-submodule `Nᴳ := (Representation.ofDistribMulAction A G N).invariants`. The statements
assume the instance `SMulCommClass G A N` that this submodule needs, and the lemma supplies it
where it is not already found. The two constructions are

  `N ↦ Nᴳ`  and  `M ↦ B ⊗[A] M`, with `G` acting on the left factor.

Mathlib's action on the left factor of `B ⊗[A] M` asks for `SMulCommClass A G B`, the symmetric
form of `SMulCommClass G A B`; the statements about `B ⊗[A] M` assume both.

The descent isomorphisms are

* `B ⊗[A] Nᴳ ≃ₗ[B] N`, `b ⊗ n ↦ b • n`, for every `B`-module with semilinear action
  (`TauCeti.MulSemiringAction.baseChangeInvariantsEquiv`);
* `M ≃ₗ[A] (B ⊗[A] M)ᴳ`, `m ↦ 1 ⊗ m`, for every `A`-module, when moreover `A → B` is injective
  (`TauCeti.MulSemiringAction.invariantsBaseChangeEquiv`). This one only needs an element of
  trace `1` in place of freeness, so it also covers non-free actions with `|G|` invertible.

The first needs no injectivity of `A → B`. The second does: for `A = A₁ × A₂` acting on a torsor
`B` over `A₁` through the first factor, the invariants of `B ⊗[A] A = B` are `A₁`, not `A`.

Both proofs are explicit. Freeness gives elements `xᵢ, yᵢ ∈ B` with
`∑ i, xᵢ * g • yᵢ = 1` for `g = 1` and `0` otherwise, and then every `n ∈ N` is
`n = ∑ i, xᵢ • ∑ g, g • (yᵢ • n)` (`TauCeti.MulSemiringAction.sum_smul_sum_smul_smul`), which
inverts the first map. For the second, an element `c ∈ B` of trace `∑ g, g • c = 1`, which exists
for a free action (`TauCeti.MulSemiringAction.exists_sum_smul_eq_one`), gives the `A`-linear
retraction `b ↦ ∑ g, g • (c * b)` of `A → B` (`TauCeti.MulSemiringAction.traceCoord`), and every
invariant `z ∈ B ⊗[A] M` is
`z = ∑ g, g • (c • z)`, which is `1 ⊗ m` for the image `m` of `z` under that retraction.

## Main definitions

* `TauCeti.MulSemiringAction.baseChangeInvariantsEquiv`: `B ⊗[A] Nᴳ ≃ₗ[B] N`.
* `TauCeti.MulSemiringAction.invariantsBaseChangeEquiv`: `M ≃ₗ[A] (B ⊗[A] M)ᴳ`.

## Main results

* `TauCeti.MulSemiringAction.smulCommClass_of_smulDistribClass`: a `B`-semilinear action is
  `A`-linear, so its invariants form an `A`-submodule.
* `TauCeti.MulSemiringAction.smulDistribClass_tensorProduct`: the action of `G` on the left factor
  of `B ⊗[A] M` is `B`-semilinear.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, §1.
-/

public section

open TensorProduct

namespace TauCeti.MulSemiringAction

section SemilinearAction

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- A `B`-semilinear action of `G` on `N` is `A`-linear, since `G` fixes the image of `A`. Thus
the invariants of `N` form an `A`-submodule. -/
theorem smulCommClass_of_smulDistribClass (N : Type*) [AddCommMonoid N] [Module A N] [Module B N]
    [IsScalarTower A B N] [DistribMulAction G N] [SMulDistribClass G B N] :
    SMulCommClass G A N where
  smul_comm g a n := by
    rw [← algebraMap_smul B a n, smul_distrib_smul, smul_algebraMap, algebraMap_smul]

end SemilinearAction

section TensorProduct

variable (A B G : Type*) [CommSemiring A] [CommSemiring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass A G B] (M : Type*) [AddCommMonoid M] [Module A M]

/-- The action of `G` on the left factor of `B ⊗[A] M` is `B`-semilinear. -/
instance smulDistribClass_tensorProduct : SMulDistribClass G B (B ⊗[A] M) where
  smul_distrib_smul g b z := by
    induction z using TensorProduct.inductionOn with
    | tmul x m => simp [smul_tmul', smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]

end TensorProduct

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

section BaseChangeInvariants

variable (A B G) (N : Type*) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [DistribMulAction G N] [SMulDistribClass G B N] [SMulCommClass G A N]

omit [SMulCommClass G A B] in
/-- The trace of `b • m` for an invariant `m` is `a • m`, where `a ∈ A` is the trace of `b`. -/
private theorem trace_smul_of_mem_invariants [Fintype G] [Algebra.IsInvariant A B G] (b : B)
    {m : N} (hm : m ∈ (Representation.ofDistribMulAction A G N).invariants) :
    ∃ a : A, algebraMap A B a = ∑ g : G, g • b ∧
      (Representation.ofDistribMulAction A G N).normInvariants (b • m) = a • ⟨m, hm⟩ := by
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) _ (smul_sum_smul (G := G) · b)
  refine ⟨a, ha, Subtype.ext ?_⟩
  have hm' (g : G) : g • m = m := by simpa using hm g
  simp only [Representation.coe_normInvariants_apply, Representation.norm_ofDistribMulAction_eq,
    smul_distrib_smul, hm', Submodule.coe_smul, ← algebraMap_smul B a m, ha,
    Finset.sum_smul]

variable {A B G N}

/-- The descent map `B ⊗[A] Nᴳ → N`, `b ⊗ n ↦ b • n`, is bijective for a free action with ring of
invariants `A`. Its inverse is `n ↦ ∑ i, xᵢ ⊗ ∑ g, g • (yᵢ • n)` for a dual basis `xᵢ, yᵢ`. -/
private theorem bijective_liftBaseChange_subtype_invariants [Finite G] [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) :
    Function.Bijective
      ((Representation.ofDistribMulAction A G N).invariants.subtype.liftBaseChange B) := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨u, hu⟩ := (tensorToPi_surjective_iff (R := A)).mpr hG (Pi.single 1 1)
  obtain ⟨S, hS⟩ := exists_finset_sum_mul_smul hu
  set φ := (Representation.ofDistribMulAction A G N).invariants.subtype.liftBaseChange B
  -- The explicit inverse `ψ`.
  set ψ : N → B ⊗[A] (Representation.ofDistribMulAction A G N).invariants :=
    fun n ↦ ∑ p ∈ S, p.1 ⊗ₜ (Representation.ofDistribMulAction A G N).normInvariants (p.2 • n)
  have hψ (z) : ψ (φ z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      have key (p : B × B) :
          p.1 ⊗ₜ[A] (Representation.ofDistribMulAction A G N).normInvariants (p.2 • φ (b ⊗ₜ m)) =
          (p.1 * ∑ g : G, g • (p.2 * b)) ⊗ₜ m := by
        obtain ⟨a, ha, h⟩ := trace_smul_of_mem_invariants A B G N (p.2 * b) m.2
        simp only [φ, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, smul_smul, h,
          tmul_smul, smul_tmul', Algebra.smul_def, ← ha, mul_comm _ p.1]
      -- The dual basis identity for `B` itself, acting on itself by multiplication.
      have hb := sum_smul_sum_smul_smul hS b
      simp only [smul_eq_mul] at hb
      simp only [ψ, key, ← sum_tmul, hb]
    | add x y hx hy =>
      simp only [ψ, map_add, smul_add, tmul_add, Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy]
  refine ⟨Function.LeftInverse.injective hψ, fun n ↦ ⟨ψ n, ?_⟩⟩
  simp only [ψ, map_sum, φ, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply,
    Representation.coe_normInvariants_apply, Representation.norm_ofDistribMulAction_eq]
  exact sum_smul_sum_smul_smul hS n

variable (A B G N) in
/-- **Galois descent of modules.** For a free action of a finite group `G` on `B` with ring of
invariants `A`, every `B`-module `N` with a semilinear action of `G` is the base change of its
invariants: `B ⊗[A] Nᴳ ≃ₗ[B] N`, `b ⊗ n ↦ b • n`. -/
noncomputable def baseChangeInvariantsEquiv [Finite G] [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) :
    B ⊗[A] (Representation.ofDistribMulAction A G N).invariants ≃ₗ[B] N :=
  .ofBijective _ (bijective_liftBaseChange_subtype_invariants hG)

@[simp]
theorem baseChangeInvariantsEquiv_tmul [Finite G] [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) (b : B)
    (n : (Representation.ofDistribMulAction A G N).invariants) :
    baseChangeInvariantsEquiv A B G N hG (b ⊗ₜ n) = b • (n : N) := by
  simp [baseChangeInvariantsEquiv]

end BaseChangeInvariants

section InvariantsBaseChange

/- `G` acts on the left factor of `B ⊗[A] M` through Mathlib's `TensorProduct.leftHasSMul`,
which asks for the commutation of `A` and `G` in this order. -/
variable [SMulCommClass A G B]

variable (A B G) (M : Type*) [AddCommGroup M] [Module A M]

/-- The map `m ↦ 1 ⊗ m` from `M` to the invariants of `B ⊗[A] M`. -/
private noncomputable def oneTmul :
    M →ₗ[A] (Representation.ofDistribMulAction A G (B ⊗[A] M)).invariants :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m ↦
    (Representation.mem_invariants _ _).mpr fun g ↦ by simp [smul_tmul']

variable {A B G M}

/-- For a finite group with ring of invariants `A ⊆ B` and an element of `B` of trace `1`, the map
`m ↦ 1 ⊗ m` identifies `M` with the invariants of `B ⊗[A] M`. -/
private theorem bijective_oneTmul [Fintype G] [FaithfulSMul A B] [Algebra.IsInvariant A B G]
    (hc : ∃ c : B, ∑ g : G, g • c = 1) :
    Function.Bijective (oneTmul A B G M) := by
  obtain ⟨c, hc⟩ := hc
  -- The `A`-linear retraction `r : b ↦ ∑ g, g • (c * b)` of `A → B`.
  set r : B →ₗ[A] A := traceCoord G c
  have hr (b : B) : algebraMap A B (r b) = ∑ g : G, g • (c * b) := algebraMap_traceCoord c b
  have hr1 : r 1 = 1 := FaithfulSMul.algebraMap_injective A B <| by simp [hr, hc]
  -- The retraction `Φ : b ⊗ m ↦ r b • m` of `m ↦ 1 ⊗ m`.
  set Φ : B ⊗[A] M →ₗ[A] M := TensorProduct.lid A M ∘ₗ r.rTensor M
  have hΦ (z : B ⊗[A] M) : ∑ g : G, g • (c • z) = 1 ⊗ₜ Φ z := by
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      simp only [Φ, smul_tmul', smul_eq_mul, ← sum_tmul, ← hr, Algebra.algebraMap_eq_smul_one,
        smul_tmul, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul]
    | add x y hx hy => simp only [smul_add, Finset.sum_add_distrib, hx, hy, map_add, tmul_add]
  refine ⟨fun m m' h ↦ ?_, fun z ↦ ⟨Φ z, Subtype.ext ?_⟩⟩
  · have h' := congr_arg (Φ ∘ Subtype.val) h
    simpa [oneTmul, Φ, hr1] using h'
  · -- An invariant `z` is `(∑ g, g • c) • z = ∑ g, g • (c • z)`.
    have hz (g : G) : g • (z : B ⊗[A] M) = z := by simpa using z.2 g
    calc (oneTmul A B G M (Φ z) : B ⊗[A] M) = ∑ g : G, g • (c • (z : B ⊗[A] M)) := by
          simp [oneTmul, hΦ]
      _ = (z : B ⊗[A] M) := by
          simp only [smul_distrib_smul, hz, ← Finset.sum_smul, hc, one_smul]

variable (A B G M) in
/-- **Galois descent of modules.** For a finite group `G` acting on `B` with ring of invariants
`A ⊆ B`, and an element of `B` of trace `1` (as for a free action, by `exists_sum_smul_eq_one`),
every `A`-module `M` is recovered as the invariants of its base change:
`M ≃ₗ[A] (B ⊗[A] M)ᴳ`, `m ↦ 1 ⊗ m`, with `G` acting on the left factor. -/
noncomputable def invariantsBaseChangeEquiv [Fintype G] [FaithfulSMul A B]
    [Algebra.IsInvariant A B G] (hc : ∃ c : B, ∑ g : G, g • c = 1) :
    M ≃ₗ[A] (Representation.ofDistribMulAction A G (B ⊗[A] M)).invariants :=
  .ofBijective _ (bijective_oneTmul hc)

@[simp]
theorem coe_invariantsBaseChangeEquiv_apply [Fintype G] [FaithfulSMul A B]
    [Algebra.IsInvariant A B G] (hc : ∃ c : B, ∑ g : G, g • c = 1) (m : M) :
    (invariantsBaseChangeEquiv A B G M hc m : B ⊗[A] M) = 1 ⊗ₜ m := (rfl)

end InvariantsBaseChange

end TauCeti.MulSemiringAction
