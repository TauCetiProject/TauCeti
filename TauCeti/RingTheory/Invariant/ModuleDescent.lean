/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RingTheory.Invariant.Free
import Mathlib.LinearAlgebra.TensorProduct.Lift
import TauCeti.RingTheory.Invariant.Basic

/-!
# Galois descent of modules along a free action of a finite group

Let a finite group `G` act freely on a commutative `A`-algebra `B` by `A`-algebra automorphisms
with ring of invariants `A`; by Chase–Harrison–Rosenberg this says that `B` is a finite étale
`G`-torsor over `A` (`TauCeti.Algebra.isFiniteEtaleTorsor_iff`), up to injectivity of `A → B`.
This file proves finite Galois descent for modules: `A`-modules are the same as `B`-modules with
a semilinear action of `G`.

A *semilinear* action on a `B`-module `N` is a distributive action of `G` with
`g • (b • n) = (g • b) • (g • n)` (Mathlib's `SMulDistribClass G B N`). Such an action is
`A`-linear (`TauCeti.MulSemiringAction.smulCommClass_of_smulDistribClass`), so its invariants form
the `A`-submodule `Nᴳ := (Representation.ofDistribMulAction A G N).invariants`. The statements
assume the instance `SMulCommClass G A N` that this submodule needs, and the lemma supplies it
where it is not already found. The two functors are

  `N ↦ Nᴳ`  and  `M ↦ B ⊗[A] M`, with `G` acting on the left factor.

Mathlib's action on the left factor of `B ⊗[A] M` asks for `SMulCommClass A G B`, the symmetric
form of the standing assumption `SMulCommClass G A B`.

The descent isomorphisms are

* `B ⊗[A] Nᴳ ≃ₗ[B] N`, `b ⊗ n ↦ b • n`, for every `B`-module with semilinear action
  (`TauCeti.MulSemiringAction.baseChangeInvariantsEquiv`);
* `M ≃ₗ[A] (B ⊗[A] M)ᴳ`, `m ↦ 1 ⊗ m`, for every `A`-module, when moreover `A → B` is injective
  (`TauCeti.MulSemiringAction.invariantsBaseChangeEquiv`).

The first needs no injectivity of `A → B`. The second does: for `A = A₁ × A₂` acting on a torsor
`B` over `A₁` through the first factor, the invariants of `B ⊗[A] A = B` are `A₁`, not `A`.

Both proofs are explicit. Freeness gives elements `xᵢ, yᵢ ∈ B` with
`∑ i, xᵢ * g • yᵢ = 1` for `g = 1` and `0` otherwise, and then every `n ∈ N` is
`n = ∑ i, xᵢ • ∑ g, g • (yᵢ • n)`, which inverts the first map. For the second, an element
`c ∈ B` of trace `∑ g, g • c = 1` (`TauCeti.MulSemiringAction.exists_sum_smul_eq_one`) gives the
`A`-linear retraction `b ↦ ∑ g, g • (c * b)` of `A → B`, and every invariant `z ∈ B ⊗[A] M` is
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

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

variable (A B G) in
/-- A `B`-semilinear action of `G` on `N` is `A`-linear, since `G` fixes the image of `A`. Thus
the invariants of `N` form an `A`-submodule. -/
theorem smulCommClass_of_smulDistribClass (N : Type*) [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] [DistribMulAction G N] [SMulDistribClass G B N] :
    SMulCommClass G A N where
  smul_comm g a n := by
    rw [← algebraMap_smul B a n, smul_distrib_smul, smul_algebraMap, algebraMap_smul]

section DualBasis

variable {N : Type*} [AddCommGroup N] [Module B N] [DistribMulAction G N]
  [SMulDistribClass G B N]

/-- The dual basis identity `n = ∑ i, xᵢ • ∑ g, g • (yᵢ • n)` for a `B`-module with semilinear
action, where `∑ i, xᵢ * g • yᵢ` is the indicator function of `1`. -/
private theorem sum_smul_sum_smul_smul [Fintype G] [DecidableEq G] {S : Finset (B × B)}
    (hS : ∀ g : G, ∑ p ∈ S, p.1 * g • p.2 = (Pi.single 1 1 : G → B) g) (n : N) :
    ∑ p ∈ S, p.1 • ∑ g : G, g • (p.2 • n) = n := by
  simp only [Finset.smul_sum, smul_distrib_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hS]
  simp [Pi.single_apply]

end DualBasis

section BaseChangeInvariants

variable (A B G) (N : Type*) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  [DistribMulAction G N] [SMulDistribClass G B N] [SMulCommClass G A N]

/-- The trace `n ↦ ∑ g, g • n`, as an `A`-linear map into the invariants. -/
private noncomputable def trace [Fintype G] :
    N →ₗ[A] (Representation.ofDistribMulAction A G N).invariants :=
  (Representation.ofDistribMulAction A G N).norm.codRestrict _ fun n ↦
    (Representation.mem_invariants _ _).mpr fun g ↦ by
      rw [Representation.ofDistribMulAction_apply_apply,
        Representation.norm_ofDistribMulAction_eq]
      exact smul_sum_smul g n

private theorem coe_trace [Fintype G] (n : N) : (trace A G N n : N) = ∑ g : G, g • n := by
  rw [trace, LinearMap.codRestrict_apply, Representation.norm_ofDistribMulAction_eq]

omit [SMulCommClass G A B] in
/-- The trace of `b • m` for an invariant `m` is `a • m`, where `a ∈ A` is the trace of `b`. -/
private theorem trace_smul_of_mem_invariants [Fintype G] [Algebra.IsInvariant A B G] (b : B)
    {m : N} (hm : m ∈ (Representation.ofDistribMulAction A G N).invariants) :
    ∃ a : A, algebraMap A B a = ∑ g : G, g • b ∧ trace A G N (b • m) = a • ⟨m, hm⟩ := by
  obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) _ (smul_sum_smul (G := G) · b)
  refine ⟨a, ha, Subtype.ext ?_⟩
  have hm' (g : G) : g • m = m := by simpa using hm g
  simp only [coe_trace, smul_distrib_smul, hm', Submodule.coe_smul, ← algebraMap_smul B a m, ha,
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
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
  have hS (g : G) : ∑ p ∈ S, p.1 * g • p.2 = (Pi.single 1 1 : G → B) g := by
    simpa using congr_fun hu g
  set φ := (Representation.ofDistribMulAction A G N).invariants.subtype.liftBaseChange B
  -- The explicit inverse `ψ`.
  set ψ : N → B ⊗[A] (Representation.ofDistribMulAction A G N).invariants :=
    fun n ↦ ∑ p ∈ S, p.1 ⊗ₜ trace A G N (p.2 • n)
  have hψ (z) : ψ (φ z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      have key (p : B × B) : p.1 ⊗ₜ[A] trace A G N (p.2 • φ (b ⊗ₜ m)) =
          (p.1 * ∑ g : G, g • (p.2 * b)) ⊗ₜ m := by
        obtain ⟨a, ha, h⟩ := trace_smul_of_mem_invariants A B G N (p.2 * b) m.2
        simp only [φ, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, smul_smul, h,
          tmul_smul, smul_tmul', Algebra.smul_def, ← ha, mul_comm _ p.1]
      -- The dual basis identity for `B` itself, acting on itself by multiplication.
      have : SMulDistribClass G B B := ⟨fun g x y ↦ smul_mul' g x y⟩
      have hb := sum_smul_sum_smul_smul hS b
      simp only [smul_eq_mul] at hb
      simp only [ψ, key, ← sum_tmul, hb]
    | add x y hx hy =>
      simp only [ψ, map_add, smul_add, tmul_add, Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy]
  refine ⟨Function.LeftInverse.injective hψ, fun n ↦ ⟨ψ n, ?_⟩⟩
  simp only [ψ, map_sum, φ, LinearMap.liftBaseChange_tmul, Submodule.subtype_apply, coe_trace]
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

/-- `G` acts on the left factor of `B ⊗[A] M` through Mathlib's `TensorProduct.leftHasSMul`,
which asks for the commutation of `A` and `G` in this order. -/
local instance : SMulCommClass A G B := .symm _ _ _

variable (A B G) (M : Type*) [AddCommGroup M] [Module A M]

/-- The action of `G` on the left factor of `B ⊗[A] M` is `B`-semilinear. -/
instance smulDistribClass_tensorProduct : SMulDistribClass G B (B ⊗[A] M) where
  smul_distrib_smul g b z := by
    induction z using TensorProduct.inductionOn with
    | tmul x m => simp [smul_tmul', smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]

variable {A B G} in
/-- For a free action with ring of invariants `A ⊆ B`, some `c ∈ B` of trace `1` gives an
`A`-linear retraction `b ↦ ∑ g, g • (c * b)` of `A → B`. -/
private theorem exists_sum_smul_eq_one_and_retraction [Finite G] [FaithfulSMul A B]
    [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) :
    ∃ (_ : Fintype G) (c : B) (r : B →ₗ[A] A), ∑ g : G, g • c = 1 ∧
      ∀ b, algebraMap A B (r b) = ∑ g : G, g • (c * b) := by
  have := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one hG
  choose φ hφ using fun b : B ↦
    Algebra.IsInvariant.isInvariant (A := A) _ (smul_sum_smul (G := G) · (c * b))
  have inj := FaithfulSMul.algebraMap_injective A B
  refine ⟨this, c,
    { toFun := φ
      map_add' b b' := inj <| by simp [hφ, mul_add, Finset.sum_add_distrib]
      map_smul' a b := inj <| by
        simp only [hφ, mul_smul_comm, smul_comm _ a, ← Finset.smul_sum]
        simp only [RingHom.id_apply, smul_eq_mul, map_mul, hφ, Algebra.smul_def] },
    hc, hφ⟩

/-- The map `m ↦ 1 ⊗ m` from `M` to the invariants of `B ⊗[A] M`. -/
private noncomputable def oneTmul :
    M →ₗ[A] (Representation.ofDistribMulAction A G (B ⊗[A] M)).invariants :=
  (TensorProduct.mk A B M 1).codRestrict _ fun m ↦
    (Representation.mem_invariants _ _).mpr fun g ↦ by simp [smul_tmul']

variable {A B G M}

/-- For a free action of a finite group with ring of invariants `A ⊆ B`, the map `m ↦ 1 ⊗ m`
identifies `M` with the invariants of `B ⊗[A] M`. -/
private theorem bijective_oneTmul [Finite G] [FaithfulSMul A B] [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) :
    Function.Bijective (oneTmul A B G M) := by
  obtain ⟨_, c, r, hc, hr⟩ := exists_sum_smul_eq_one_and_retraction (A := A) hG
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
/-- **Galois descent of modules.** For a free action of a finite group `G` on `B` with ring of
invariants `A`, and `A → B` injective, every `A`-module `M` is recovered as the invariants of
its base change: `M ≃ₗ[A] (B ⊗[A] M)ᴳ`, `m ↦ 1 ⊗ m`, with `G` acting on the left factor. -/
noncomputable def invariantsBaseChangeEquiv [Finite G] [FaithfulSMul A B]
    [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) :
    M ≃ₗ[A] (Representation.ofDistribMulAction A G (B ⊗[A] M)).invariants :=
  .ofBijective _ (bijective_oneTmul hG)

@[simp]
theorem coe_invariantsBaseChangeEquiv_apply [Finite G] [FaithfulSMul A B]
    [Algebra.IsInvariant A B G]
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤) (m : M) :
    (invariantsBaseChangeEquiv A B G M hG m : B ⊗[A] M) = 1 ⊗ₜ m := (rfl)

end InvariantsBaseChange

end TauCeti.MulSemiringAction
