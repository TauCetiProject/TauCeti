/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Endomorphisms preserving a submodule family and their centralizer

For a family of submodules, the family-invariant endomorphisms are those preserving each member.
An automorphism permuting the family preserves this space under conjugation. Over a field, if one
member is disjoint from the sum of the others, every subspace of that member is the range of a
family-invariant projection. Consequently an automorphism commuting with the scalar extensions
of all family-invariant endomorphisms preserves the scalar extension of every such subspace.

The scalar-extension statement allows arbitrary coefficient algebras, including nonreduced
ones. It supplies the linear-algebra step in the normal-subgroup kernel argument: subgroup
points act by scalars on character spaces, and centralizing their family-invariant endomorphisms
forces preservation of a Chevalley line inside one character space.

The construction uses Mathlib's `Submodule.compatibleMaps`, `Submodule.projection`, and
`LinearMap.IsIdempotentElem.commute_iff_of_isUnit`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §11.5.
* A. Borel, *Linear Algebraic Groups*, §5.5.
-/

public section

open scoped TensorProduct

namespace Submodule

section Semiring

variable {R V ι : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The endomorphisms preserving every submodule in a family. For a direct-sum decomposition,
these are exactly the block-diagonal endomorphisms. -/
def familyInvariant (S : ι → Submodule R V) : Submodule R (Module.End R V) :=
  ⨅ i, (S i).compatibleMaps (S i)

/-- A family-invariant endomorphism preserves each member. -/
@[simp]
theorem mem_familyInvariant {S : ι → Submodule R V} {f : Module.End R V} :
    f ∈ familyInvariant S ↔ ∀ i, ∀ v ∈ S i, f v ∈ S i := by
  simp [familyInvariant, compatibleMaps, Submodule.mem_iInf, IsConcreteLE.le_iff]

/-- Family-invariant endomorphisms are closed under composition. -/
theorem mul_mem_familyInvariant {S : ι → Submodule R V} {f g : Module.End R V}
    (hf : f ∈ familyInvariant S) (hg : g ∈ familyInvariant S) :
    f * g ∈ familyInvariant S := by
  exact mem_familyInvariant.mpr fun i v hv ↦
    mem_familyInvariant.mp hf i _ (mem_familyInvariant.mp hg i v hv)

/-- Conjugation by an automorphism permuting the family preserves family-invariant endomorphisms.
No independence or spanning assumption is needed. -/
theorem conj_mem_familyInvariant (S : ι → Submodule R V) (e : V ≃ₗ[R] V) (σ : Equiv.Perm ι)
    (he : ∀ i, (S i).map e.toLinearMap = S (σ i)) {f : Module.End R V}
    (hf : f ∈ familyInvariant S) : e.conjAlgEquiv R f ∈ familyInvariant S := by
  refine mem_familyInvariant.mpr fun i ↦ ?_
  rw [← Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  have hmap : (S (σ.symm i)).map e.toLinearMap = S i := by
    simpa only [σ.apply_symm_apply] using he (σ.symm i)
  rw [← hmap, LinearEquiv.conjAlgEquiv_apply]
  exact e.map_mem_invtSubmodule_conj_iff.mpr
    ((f.mem_invtSubmodule_iff_forall_mem_of_mem).mpr (mem_familyInvariant.mp hf _))

/-- An automorphism permuting the family maps the space of family-invariant endomorphisms onto
itself under conjugation. -/
theorem map_conj_familyInvariant (S : ι → Submodule R V) (e : V ≃ₗ[R] V) (σ : Equiv.Perm ι)
    (he : ∀ i, (S i).map e.toLinearMap = S (σ i)) :
    (familyInvariant S).map (e.conjAlgEquiv R).toLinearMap = familyInvariant S := by
  have he' (i) : (S i).map e.symm.toLinearMap = S (σ.symm i) := by
    apply (Submodule.map_symm_eq_iff e).mpr
    simpa using he (σ.symm i)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact conj_mem_familyInvariant S e σ he hf
  · intro f hf
    refine ⟨e.symm.conjAlgEquiv R f, conj_mem_familyInvariant S e.symm σ.symm he' hf, ?_⟩
    simp [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_assoc]

/-- If an operator acts by a scalar on each member of a spanning family, it commutes with every
scalar-extended family-invariant endomorphism. The scalars may belong to the coefficient algebra;
no independence or finiteness of the family is needed. -/
theorem commute_baseChange_of_forall_tmul_eq_smul {A : Type*} [Semiring A] [Algebra R A]
    (S : ι → Submodule R V) (hS : ⨆ i, S i = ⊤)
    (T : Module.End A (A ⊗[R] V)) (c : ι → A)
    (hT : ∀ i, ∀ v ∈ S i, T (1 ⊗ₜ[R] v) = c i • (1 ⊗ₜ[R] v))
    {f : Module.End R V} (hf : f ∈ familyInvariant S) : Commute T (f.baseChange A) := by
  have hx (v : V) : T (1 ⊗ₜ[R] f v) = f.baseChange A (T (1 ⊗ₜ[R] v)) := by
    have hv : v ∈ ⨆ i, S i := hS ▸ mem_top
    induction hv using Submodule.iSup_induction' with
    | mem i v hv =>
        rw [hT i _ (mem_familyInvariant.mp hf i v hv), hT i v hv]
        simp
    | zero => simp
    | add x y _ _ hx hy => simp [TensorProduct.tmul_add, hx, hy]
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [Module.End.mul_apply, map_add] using congrArg₂ (· + ·) hx hy
  | tmul a v =>
      simp only [Module.End.mul_apply, LinearMap.baseChange_tmul]
      simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        congrArg (a • ·) (hx v)

end Semiring

section Field

variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Every subspace of a family member disjoint from the sum of the other members is the range of
a family-invariant idempotent, even when the family does not span the ambient space. -/
theorem exists_projection_mem_familyInvariant (S : ι → Submodule k V) (i : ι)
    (hS : Disjoint (S i) (⨆ j, ⨆ (_ : j ≠ i), S j)) (L : Submodule k V) (hL : L ≤ S i) :
    ∃ p ∈ familyInvariant S, IsIdempotentElem p ∧ LinearMap.range p = L := by
  obtain ⟨Q, hQ, hcompl⟩ := (hS.mono_left hL).symm.exists_isCompl
  let p := L.projection Q hcompl.symm
  refine ⟨p, mem_familyInvariant.mpr ?_, L.isIdempotentElem_projection hcompl.symm,
    L.range_projection hcompl.symm⟩
  intro j v hv
  by_cases hji : j = i
  · subst j
    exact hL (L.projection_apply_mem hcompl.symm v)
  · have hvQ : v ∈ Q := hQ (mem_iSup_of_mem j (mem_iSup_of_mem hji hv))
    rw [L.projection_apply_of_mem_right hcompl.symm hvQ]
    exact (S j).zero_mem

variable {A : Type*} [Ring A] [Algebra k A]

/-- An automorphism commuting with every scalar-extended family-invariant endomorphism preserves
any scalar-extended subspace of a family member disjoint from the sum of the other members.
This tests arbitrary algebra-valued automorphisms rather than just rational points. -/
theorem map_baseChange_eq_of_forall_commute_familyInvariant
    (S : ι → Submodule k V) (i : ι)
    (hS : Disjoint (S i) (⨆ j, ⨆ (_ : j ≠ i), S j)) (L : Submodule k V) (hL : L ≤ S i)
    (e : (A ⊗[k] V) ≃ₗ[A] (A ⊗[k] V))
    (he : ∀ p ∈ familyInvariant S, Commute e.toLinearMap (p.baseChange A)) :
    (L.baseChange A).map e.toLinearMap = L.baseChange A := by
  obtain ⟨p, hp, hid, hrange⟩ := exists_projection_mem_familyInvariant S i hS L hL
  have hid' : IsIdempotentElem (p.baseChange A) :=
    hid.map (Module.End.baseChangeHom k A V)
  have hrange' : LinearMap.range (p.baseChange A) = L.baseChange A := by
    rw [← hrange]
    ext x
    simpa only [Submodule.baseChange, LinearMap.mem_range, LinearMap.baseChange_eq_ltensor] using
      SetLike.ext_iff.mp (LinearMap.lTensor_range (Q := A) (g := p)) x
  rw [← hrange']
  have heunit : IsUnit e.toLinearMap := (Module.End.isUnit_iff _).mpr e.bijective
  exact ((LinearMap.IsIdempotentElem.commute_iff_of_isUnit heunit hid').mp
    (he p hp).symm).1

end Field

end Submodule
