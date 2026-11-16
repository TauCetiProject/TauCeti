/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.Submodule.Relation.Basic

/-!
# Matching spaces and excess of linear relations

For relations `L ⊆ M × N` and `K ⊆ N × P`, `L.relCompFiberProduct K` consists of pairs
of relation vectors with equal middle coordinates. The endpoint projection onto `L.relComp K`
is surjective. Its kernel is canonically the **excess**
`{n | (0, n) ∈ L ∧ (n, 0) ∈ K}`. Thus dividing the matching space by the embedded excess
identifies it with the composite, even when the projection is not injective.

This is the linear algebra of clean composition of correspondences: matching tangent vectors
are quotiented by the vectors invisible to both outer projections. No symplectic structure is
needed for the quotient construction.

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
-/

public section

namespace Submodule

section Semiring

variable {R M N P : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Pairs of relation vectors with equal middle coordinates. -/
def relCompFiberProduct (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    Submodule R ((M × N) × (N × P)) :=
  (L.prod K) ⊓ LinearMap.eqLocus
    ((LinearMap.snd R M N).comp (LinearMap.fst R (M × N) (N × P)))
    ((LinearMap.fst R N P).comp (LinearMap.snd R (M × N) (N × P)))

/-- The matching space is the product relation cut out by equality of middle coordinates. -/
theorem relCompFiberProduct_def (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    L.relCompFiberProduct K = (L.prod K) ⊓ LinearMap.eqLocus
      ((LinearMap.snd R M N).comp (LinearMap.fst R (M × N) (N × P)))
      ((LinearMap.fst R N P).comp (LinearMap.snd R (M × N) (N × P))) := (rfl)

/-- Membership in the matching space records both relations and equality in the middle. -/
@[simp]
theorem mem_relCompFiberProduct {L : Submodule R (M × N)} {K : Submodule R (N × P)}
    {z : (M × N) × (N × P)} :
    z ∈ L.relCompFiberProduct K ↔ z.1 ∈ L ∧ z.2 ∈ K ∧ z.1.2 = z.2.1 := by
  simp [relCompFiberProduct, and_assoc]

/-- The endpoint projection of matching relation vectors onto the composite relation. -/
def relCompProjection (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    L.relCompFiberProduct K →ₗ[R] L.relComp K where
  toFun z := ⟨(z.1.1.1, z.1.2.2),
    mem_relComp.mpr ⟨z.1.1.2, (mem_relCompFiberProduct.mp z.2).1,
      (mem_relCompFiberProduct.mp z.2).2.2 ▸ (mem_relCompFiberProduct.mp z.2).2.1⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The endpoint projection forgets the common middle coordinate. -/
@[simp]
theorem relCompProjection_apply (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (z : L.relCompFiberProduct K) :
    (L.relCompProjection K z : M × P) = (z.1.1.1, z.1.2.2) := (rfl)

/-- Every vector in the composite has a matching lift. -/
theorem relCompProjection_surjective (L : Submodule R (M × N))
    (K : Submodule R (N × P)) : Function.Surjective (L.relCompProjection K) := by
  rintro ⟨⟨m, p⟩, h⟩
  obtain ⟨n, hnL, hnK⟩ := mem_relComp.mp h
  exact ⟨⟨((m, n), (n, p)), mem_relCompFiberProduct.mpr ⟨hnL, hnK, rfl⟩⟩, rfl⟩

/-- A matching pair projects to zero exactly when both of its endpoints vanish. -/
@[simp]
theorem relCompProjection_eq_zero {L : Submodule R (M × N)} {K : Submodule R (N × P)}
    {z : L.relCompFiberProduct K} :
    L.relCompProjection K z = 0 ↔ z.1.1.1 = 0 ∧ z.1.2.2 = 0 := by
  rw [← coe_eq_zero, relCompProjection_apply, Prod.mk_eq_zero]

/-- The endpoint projection onto the composite is onto. -/
@[simp]
theorem range_relCompProjection (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    LinearMap.range (L.relCompProjection K) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ (L.relCompProjection_surjective K)

/-- The excess consists of middle vectors that occur with zero at both endpoints. -/
def relCompExcess (L : Submodule R (M × N)) (K : Submodule R (N × P)) : Submodule R N :=
  L.comap (LinearMap.inr R M N) ⊓ K.comap (LinearMap.inl R N P)

/-- The excess is the intersection of the middle slices of the two relations. -/
theorem relCompExcess_def (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    L.relCompExcess K = L.comap (LinearMap.inr R M N) ⊓ K.comap (LinearMap.inl R N P) := (rfl)

/-- A middle vector is in the excess exactly when both zero-endpoint pairs lie in the relations. -/
@[simp]
theorem mem_relCompExcess {L : Submodule R (M × N)} {K : Submodule R (N × P)} {n : N} :
    n ∈ L.relCompExcess K ↔ (0, n) ∈ L ∧ (n, 0) ∈ K := Iff.rfl

/-- Embed an excess vector in the matching space by assigning it zero endpoints. -/
def relCompExcessInclusion (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    L.relCompExcess K →ₗ[R] L.relCompFiberProduct K where
  toFun n := ⟨((0, n), (n, 0)), mem_relCompFiberProduct.mpr ⟨n.2.1, n.2.2, rfl⟩⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- An embedded excess vector is the matching pair `((0, n), (n, 0))`. -/
@[simp]
theorem relCompExcessInclusion_apply (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (n : L.relCompExcess K) :
    (L.relCompExcessInclusion K n : (M × N) × (N × P)) = ((0, (n : N)), ((n : N), 0)) := (rfl)

/-- The endpoint projection kills every embedded excess vector. -/
@[simp]
theorem relCompProjection_relCompExcessInclusion (L : Submodule R (M × N))
    (K : Submodule R (N × P)) (n : L.relCompExcess K) :
    L.relCompProjection K (L.relCompExcessInclusion K n) = 0 := (rfl)

/-- The endpoint projection composed with the excess inclusion is zero. -/
@[simp]
theorem relCompProjection_comp_relCompExcessInclusion (L : Submodule R (M × N))
    (K : Submodule R (N × P)) :
    (L.relCompProjection K).comp (L.relCompExcessInclusion K) = 0 :=
  LinearMap.ext (L.relCompProjection_relCompExcessInclusion K)

/-- The excess inclusion is injective. -/
theorem relCompExcessInclusion_injective (L : Submodule R (M × N))
    (K : Submodule R (N × P)) : Function.Injective (L.relCompExcessInclusion K) := by
  intro n n' h
  exact Subtype.ext (congrArg (fun z : L.relCompFiberProduct K ↦ z.1.1.2) h)

/-- An embedded excess vector vanishes exactly when the excess vector does. -/
@[simp]
theorem relCompExcessInclusion_eq_zero {L : Submodule R (M × N)} {K : Submodule R (N × P)}
    {n : L.relCompExcess K} : L.relCompExcessInclusion K n = 0 ↔ n = 0 :=
  (L.relCompExcessInclusion K).map_eq_zero_iff (L.relCompExcessInclusion_injective K)

/-- The excess inclusion has trivial kernel. -/
@[simp]
theorem ker_relCompExcessInclusion (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    LinearMap.ker (L.relCompExcessInclusion K) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective (L.relCompExcessInclusion_injective K)

/-- The kernel of the endpoint projection is exactly the embedded excess. -/
theorem ker_relCompProjection (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    LinearMap.ker (L.relCompProjection K) = LinearMap.range (L.relCompExcessInclusion K) := by
  ext z
  constructor
  · intro hz
    have h := congrArg (fun x : L.relComp K ↦ (x : M × P)) (LinearMap.mem_ker.mp hz)
    have hm : z.1.1.1 = 0 := congrArg Prod.fst h
    have hp : z.1.2.2 = 0 := congrArg Prod.snd h
    obtain ⟨hzL, hzK, hmatch⟩ := mem_relCompFiberProduct.mp z.2
    have hn : z.1.1.2 ∈ L.relCompExcess K := by
      rw [mem_relCompExcess]
      constructor
      · rw [← hm, Prod.eta]
        exact hzL
      · rw [hmatch, ← hp, Prod.eta]
        exact hzK
    exact ⟨⟨z.1.1.2, hn⟩, by ext <;> simp [hm, hp, hmatch]⟩
  · rintro ⟨n, rfl⟩
    exact LinearMap.mem_ker.mpr (Subtype.ext rfl)

/-- The excess is canonically the kernel of the endpoint projection; the inverse reads off the
middle coordinate. -/
def relCompExcessEquivKer (L : Submodule R (M × N))
    (K : Submodule R (N × P)) :
    L.relCompExcess K ≃ₗ[R] LinearMap.ker (L.relCompProjection K) where
  toFun n := ⟨L.relCompExcessInclusion K n,
    LinearMap.mem_ker.mpr (L.relCompProjection_relCompExcessInclusion K n)⟩
  invFun z := ⟨z.1.1.1.2, by
    obtain ⟨n, hn⟩ := (L.ker_relCompProjection K ▸ z.2 :
      z.1 ∈ LinearMap.range (L.relCompExcessInclusion K))
    rw [← hn]
    exact n.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨z, hz⟩
    rw [L.ker_relCompProjection K] at hz
    obtain ⟨n, rfl⟩ := hz
    rfl

/-- The kernel identification agrees with the excess inclusion into the matching space. -/
@[simp]
theorem relCompExcessEquivKer_apply (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (n : L.relCompExcess K) :
    (L.relCompExcessEquivKer K n : L.relCompFiberProduct K) =
      L.relCompExcessInclusion K n := (rfl)

/-- The inverse kernel identification reads off the common middle coordinate. -/
@[simp]
theorem relCompExcessEquivKer_symm_apply (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (z : LinearMap.ker (L.relCompProjection K)) :
    ((L.relCompExcessEquivKer K).symm z : N) = z.1.1.1.2 := (rfl)

end Semiring

section Ring

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The endpoint projection is injective exactly when the excess vanishes. -/
theorem relCompProjection_injective_iff (L : Submodule R (M × N))
    (K : Submodule R (N × P)) :
    Function.Injective (L.relCompProjection K) ↔ L.relCompExcess K = ⊥ := by
  rw [← LinearMap.ker_eq_bot, ← subsingleton_iff_eq_bot, ← subsingleton_iff_eq_bot]
  exact (L.relCompExcessEquivKer K).toEquiv.subsingleton_congr.symm

/-- Eliminating the middle coordinate identifies the matching space modulo its embedded
excess with the composite relation. -/
noncomputable def relCompQuotientEquiv (L : Submodule R (M × N))
    (K : Submodule R (N × P)) :
    (↥(L.relCompFiberProduct K) ⧸
      LinearMap.range (L.relCompExcessInclusion K)) ≃ₗ[R] L.relComp K :=
  (Submodule.quotEquivOfEq _ _ (L.ker_relCompProjection K).symm).trans
    ((L.relCompProjection K).quotKerEquivOfSurjective (L.relCompProjection_surjective K))

/-- The quotient identification sends a matching class to its endpoint projection. -/
@[simp]
theorem relCompQuotientEquiv_apply_mk (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (z : L.relCompFiberProduct K) :
    L.relCompQuotientEquiv K (Submodule.Quotient.mk z) = L.relCompProjection K z := by
  simp [relCompQuotientEquiv]

/-- The inverse quotient identification sends an endpoint projection to its matching class. -/
@[simp]
theorem relCompQuotientEquiv_symm_apply (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (z : L.relCompFiberProduct K) :
    (L.relCompQuotientEquiv K).symm (L.relCompProjection K z) = Submodule.Quotient.mk z :=
  (LinearEquiv.symm_apply_eq _).mpr (L.relCompQuotientEquiv_apply_mk K z).symm

end Ring

section DivisionRing

variable {R M N P : Type*} [DivisionRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The dimension of the matching space is the dimension of the composite plus the excess. -/
theorem finrank_relComp_add_finrank_relCompExcess (L : Submodule R (M × N))
    (K : Submodule R (N × P)) [FiniteDimensional R (L.relCompFiberProduct K)] :
    Module.finrank R (L.relComp K) + Module.finrank R (L.relCompExcess K) =
      Module.finrank R (L.relCompFiberProduct K) := by
  have hdim := ((L.relCompProjection K).quotKerEquivOfSurjective
    (L.relCompProjection_surjective K)).finrank_eq
  rw [(L.relCompExcessEquivKer K).finrank_eq, ← hdim]
  exact Submodule.finrank_quotient_add_finrank _

end DivisionRing

end Submodule
