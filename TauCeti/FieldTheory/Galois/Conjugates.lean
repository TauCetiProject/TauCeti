/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.FieldTheory.IntermediateField.Pointwise
public import TauCeti.FieldTheory.Normal.Embeddings
public import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# Conjugate intermediate fields

Let `L / F` be a field extension, `G = L ≃ₐ[F] L`, and `K` an intermediate field with fixing
subgroup `H = K.fixingSubgroup`. The group `G` acts on the intermediate fields by
`σ • K = K.map σ` (`IntermediateField.pointwiseMulAction`, in the `Pointwise` locale), and the
subfields conjugate to `K` are the members of the orbit of `K`. This file compares that orbit with
the group theory of `H`.

* The Galois correspondence is equivariant: the fixing subgroup of `σ • K` is the conjugate
  `σ H σ⁻¹`. So the fixing subgroups of the conjugates of `K` are exactly the conjugates of `H`;
  for a Galois extension the correspondence is injective, so conjugate subfields and conjugate
  subgroups correspond bijectively.
* For a Galois extension the stabilizer of `K` is the normalizer `N_G(H)`. The conjugates of `K`
  are therefore indexed by `G ⧸ N_G(H)`, and there are `[G : N_G(H)]` of them. This is a
  proper quotient of `G ⧸ H` as soon as `H` is not self-normalizing.
* When `L / F` is normal, `G ⧸ H` is identified equivariantly with the `F`-embeddings of `K` into
  `L`, the coset of `σ` corresponding to the embedding `σ ∘ K.val`.

## Main results

* `IntermediateField.fixingSubgroup_pointwise_smul`: the fixing subgroup of `σ • K` is
  `MulAut.conj σ • K.fixingSubgroup`.
* `IntermediateField.image_fixingSubgroup_orbit`: the fixing subgroups of the conjugates of `K` are
  the conjugates of its fixing subgroup.
* `IntermediateField.mem_orbit_iff_exists_fixingSubgroup_eq`: over a Galois extension, an
  intermediate field is conjugate to `K` exactly when its fixing subgroup is conjugate to that
  of `K`.
* `IntermediateField.stabilizer_eq_normalizer`: over a Galois extension, the stabilizer of
  `K` is the normalizer of its fixing subgroup.
* `IntermediateField.orbitEquivQuotientNormalizer`,
  `IntermediateField.ncard_orbit_eq_index_normalizer`: the conjugates of `K` are indexed by the
  cosets of that normalizer, and their number is its index.
* `IntermediateField.quotientFixingSubgroupEquivAlgHom`: over a normal extension, the cosets of
  the fixing subgroup are equivariantly the `F`-embeddings of `K` into `L`.

## References

* J. S. Milne, *Fields and Galois Theory*, Chapter 3, the Galois correspondence and conjugate
  subgroups.
-/

public section

open MulAction
open scoped Pointwise

namespace IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-! ### The Galois correspondence is equivariant -/

/-- **The Galois correspondence is conjugation-equivariant.** The subgroup fixing the conjugate
field `σ(K)` is the conjugate `σ H σ⁻¹` of the subgroup `H` fixing `K`. -/
@[simp]
theorem fixingSubgroup_pointwise_smul (σ : L ≃ₐ[F] L) (K : IntermediateField F L) :
    (σ • K).fixingSubgroup = MulAut.conj σ • K.fixingSubgroup := by
  rw [algEquiv_smul_eq_map]
  exact IsGalois.map_fixingSubgroup K σ

/-- The fixing subgroups of the conjugates of `K` are exactly the conjugates of the fixing
subgroup of `K`. -/
theorem image_fixingSubgroup_orbit (K : IntermediateField F L) :
    fixingSubgroup '' orbit (L ≃ₐ[F] L) K =
      Set.range fun σ : L ≃ₐ[F] L => MulAut.conj σ • K.fixingSubgroup := by
  rw [orbit, ← Set.range_comp]
  exact congrArg Set.range (funext fun σ => fixingSubgroup_pointwise_smul σ K)

/-! ### Conjugates in a Galois extension

No finiteness is needed: by infinite Galois theory, an intermediate field of a Galois extension is
the fixed field of its fixing subgroup (`InfiniteGalois.fixedField_fixingSubgroup`). -/

section IsGalois

variable [IsGalois F L]

/-- Over a Galois extension, `σ • K = K'` exactly when the fixing subgroup of `K'` is the
conjugate by `σ` of that of `K`. -/
theorem pointwise_smul_eq_iff (σ : L ≃ₐ[F] L) (K K' : IntermediateField F L) :
    σ • K = K' ↔ MulAut.conj σ • K.fixingSubgroup = K'.fixingSubgroup := by
  rw [← fixingSubgroup_pointwise_smul]
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup (σ • K), h,
    InfiniteGalois.fixedField_fixingSubgroup]

/-- **Conjugate fields correspond to conjugate subgroups.** Over a Galois extension, an
intermediate field `K'` is conjugate to `K` exactly when its fixing subgroup is conjugate to the
fixing subgroup of `K`. With `IntermediateField.image_fixingSubgroup_orbit` and the injectivity of
the Galois correspondence, this makes `fixingSubgroup` a bijection from the conjugates of `K` onto
the conjugates of its fixing subgroup. -/
theorem mem_orbit_iff_exists_fixingSubgroup_eq (K K' : IntermediateField F L) :
    K' ∈ orbit (L ≃ₐ[F] L) K ↔
      ∃ σ : L ≃ₐ[F] L, MulAut.conj σ • K.fixingSubgroup = K'.fixingSubgroup := by
  simp only [mem_orbit_iff, pointwise_smul_eq_iff]

/-- **The stabilizer of an intermediate field is the normalizer of its fixing subgroup.** An
automorphism `σ` of a Galois extension maps `K` onto itself exactly when it normalizes the
subgroup fixing `K`. -/
theorem stabilizer_eq_normalizer (K : IntermediateField F L) :
    stabilizer (L ≃ₐ[F] L) K = Subgroup.normalizer (K.fixingSubgroup : Set (L ≃ₐ[F] L)) := by
  ext σ
  rw [mem_stabilizer_iff, pointwise_smul_eq_iff, Subgroup.mem_normalizer_iff_map_conj_eq]
  -- `MulAut.conj σ • H` is `H.map (MulAut.conj σ)`, by `Subgroup.pointwise_smul_def`.
  rfl

/-- **The conjugates of `K` are indexed by the cosets of the normalizer** of its fixing subgroup,
the coset of `σ` corresponding to `σ(K)`. -/
noncomputable def orbitEquivQuotientNormalizer (K : IntermediateField F L) :
    orbit (L ≃ₐ[F] L) K ≃
      (L ≃ₐ[F] L) ⧸ Subgroup.normalizer (K.fixingSubgroup : Set (L ≃ₐ[F] L)) :=
  (orbitEquivQuotientStabilizer (L ≃ₐ[F] L) K).trans
    (Subgroup.quotientEquivOfEq (stabilizer_eq_normalizer K))

/-- The coset of `σ` corresponds to the conjugate `σ(K)`. -/
@[simp]
theorem orbitEquivQuotientNormalizer_symm_apply (K : IntermediateField F L) (σ : L ≃ₐ[F] L) :
    ((orbitEquivQuotientNormalizer K).symm σ : IntermediateField F L) = σ • K := by
  have h : (Subgroup.quotientEquivOfEq (stabilizer_eq_normalizer K)).symm σ =
      (σ : (L ≃ₐ[F] L) ⧸ stabilizer (L ≃ₐ[F] L) K) := by
    rw [Equiv.symm_apply_eq, Subgroup.quotientEquivOfEq_mk]
  rw [orbitEquivQuotientNormalizer, Equiv.symm_trans_apply, h,
    orbitEquivQuotientStabilizer_symm_apply]

/-- **The number of conjugates of `K` is the index of the normalizer** of its fixing subgroup.
When there are infinitely many conjugates, both sides are `0`. -/
theorem ncard_orbit_eq_index_normalizer (K : IntermediateField F L) :
    (orbit (L ≃ₐ[F] L) K).ncard =
      (Subgroup.normalizer (K.fixingSubgroup : Set (L ≃ₐ[F] L))).index := by
  rw [← stabilizer_eq_normalizer, index_stabilizer]

/-- In a Galois extension, `K` is its only conjugate exactly when its fixing subgroup is a
normal subgroup. -/
theorem orbit_eq_singleton_iff_normal (K : IntermediateField F L) :
    orbit (L ≃ₐ[F] L) K = {K} ↔ K.fixingSubgroup.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, ← stabilizer_eq_normalizer, Subgroup.eq_top_iff',
    Set.eq_singleton_iff_unique_mem]
  simp only [mem_orbit_self, true_and, mem_stabilizer_iff]
  exact ⟨fun h σ => h _ (mem_orbit K σ), fun h _ ⟨σ, hσ⟩ => hσ ▸ h σ⟩

end IsGalois

/-! ### Embeddings -/

/-- The automorphisms of `L` fixing the inclusion `K →ₐ[F] L` are those fixing `K` pointwise. -/
@[simp]
theorem stabilizer_val (K : IntermediateField F L) :
    stabilizer (L ≃ₐ[F] L) K.val = K.fixingSubgroup := by
  ext σ
  rw [mem_stabilizer_iff, mem_fixingSubgroup_iff, AlgHom.ext_iff]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x x.2⟩

section Normal

variable [Normal F L]

/-- **The cosets of the fixing subgroup are the embeddings.** Over a normal extension `L / F`, the
cosets of the subgroup fixing `K` are in bijection with the `F`-embeddings of `K` into `L`, the
coset of `σ` corresponding to `σ ∘ K.val`. -/
noncomputable def quotientFixingSubgroupEquivAlgHom (K : IntermediateField F L) :
    (L ≃ₐ[F] L) ⧸ K.fixingSubgroup ≃ (K →ₐ[F] L) :=
  (Subgroup.quotientEquivOfEq (stabilizer_val K).symm).trans
    (TauCeti.quotientStabilizerEquiv (L ≃ₐ[F] L) K.val)

/-- The coset of `σ` corresponds to the embedding `σ ∘ K.val`. -/
@[simp]
theorem quotientFixingSubgroupEquivAlgHom_mk (K : IntermediateField F L) (σ : L ≃ₐ[F] L) :
    quotientFixingSubgroupEquivAlgHom K σ = σ • K.val := by
  rw [quotientFixingSubgroupEquivAlgHom, Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk]
  exact TauCeti.quotientStabilizerEquiv_mk _ _ σ

/-- The identification of the cosets with the embeddings is equivariant. -/
@[simp]
theorem quotientFixingSubgroupEquivAlgHom_smul (K : IntermediateField F L) (g : L ≃ₐ[F] L)
    (q : (L ≃ₐ[F] L) ⧸ K.fixingSubgroup) :
    quotientFixingSubgroupEquivAlgHom K (g • q) = g • quotientFixingSubgroupEquivAlgHom K q := by
  induction q using QuotientGroup.induction_on with
  | H σ => rw [Quotient.smul_mk, quotientFixingSubgroupEquivAlgHom_mk,
      quotientFixingSubgroupEquivAlgHom_mk, smul_eq_mul, mul_smul]

end Normal

end IntermediateField
