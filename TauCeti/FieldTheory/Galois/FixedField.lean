/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Fixed fields and fixing subgroups

Complements to Mathlib's Galois correspondence: when a fixed field and an intermediate field
generate the whole extension, when the correspondence survives dropping finiteness of `M / K` for
a finite subgroup, and what the correspondence gives for a cyclic subgroup.

For a finite Galois extension `M / K`, a subgroup `H ≤ Gal(M/K)` and an intermediate field `E`,
the fixed field of `H` and `E` generate `M` exactly when `H` meets the fixers of `E` trivially.

The correspondence is equivariant for conjugation: the fixed field of a conjugate subgroup is the
image of the fixed field under the conjugating automorphism.

The correspondence between subgroups and their fixed fields also holds with no hypothesis on
`M / K` at all, provided the subgroup is finite: Artin's theorem makes `M` finite Galois over the
fixed field of a finite `H`, and the fixers of that field are then exactly `H`. This is how a
subgroup of the automorphism group of an infinite extension is recovered from the field it cuts
out; the fixing subgroup of a subfield of finite degree is finite for the same reason.

The last results specialise the correspondence to a *cyclic* subgroup: the field fixed by a finite
cyclic group of automorphisms has `M` cyclic over it, and for `⟨σ⟩` there is a named automorphism
over the fixed field — `AlgEquiv.toFixedFieldAlgEquiv σ` acts on `M` as `σ` does, and generates
once `⟨σ⟩` is finite.

Neither `M / K` Galois nor `M / K` finite is needed, and neither is faithfulness of the action:
`FixedPoints.toAlgAut_surjective` asks only that the group be finite, and cyclicity passes along
its surjection. The fixed-point subfield it produces is the one underlying
`IntermediateField.fixedField`.

A simple extension `K⟮x⟯` is fixed pointwise by exactly those automorphisms that fix `x`, so
its fixing subgroup is the stabilizer of `x`; this too needs no hypothesis on `M / K` at all.

## Main results

* `Subgroup.fixedField_sup_eq_top_iff`
* `Subgroup.fixedField_map_conj`
* `IntermediateField.fixingSubgroup_fixedField_of_finite`
* `IntermediateField.finite_of_finiteDimensional_fixedField`
* `IntermediateField.card_fixingSubgroup_le`
* `IntermediateField.fixingSubgroup_adjoin_simple`
* `FixedPoints.isCyclic_algEquiv`
* `AlgEquiv.toFixedFieldAlgEquiv`, with `AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top`
-/

public section

open IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]

/-- **A trivial meet of subgroups is a full join of fields.** `M ^ H` and `E` generate `M` exactly
when `H ⊓ Gal(M/E)` is trivial.

This is the Galois correspondence read in both directions: `fixingSubgroup` turns a join of fields
into a meet of subgroups, and `fixedField` turns the trivial subgroup back into `⊤`.

Stated in the `Subgroup` namespace rather than `IntermediateField`, so that `H` — the first
explicit argument, and the one `fixedField` is applied to — carries the dot notation: a consumer
writes `H.fixedField_sup_eq_top_iff E`. -/
theorem fixedField_sup_eq_top_iff (H : Subgroup (M ≃ₐ[K] M)) (E : IntermediateField K M) :
    fixedField H ⊔ E = ⊤ ↔ H ⊓ E.fixingSubgroup = ⊥ := by
  constructor
  · intro h
    have := congrArg IntermediateField.fixingSubgroup h
    rwa [fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_top] at this
  · intro h
    have hbot : (fixedField H ⊔ E).fixingSubgroup = ⊥ := by
      rw [fixingSubgroup_sup, fixingSubgroup_fixedField, h]
    have := congrArg fixedField hbot
    rwa [IsGalois.fixedField_fixingSubgroup, fixedField_bot] at this

end Subgroup

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **A finite group of automorphisms is the whole fixing subgroup of its fixed field.** Every
`K`-automorphism of `M` that fixes `M ^ H` pointwise already lies in `H`.

Mathlib's `IntermediateField.fixingSubgroup_fixedField` is the same conclusion under
`[FiniteDimensional K M]`, which is the stronger hypothesis: a finite-dimensional `M / K` has a
finite automorphism group, so every subgroup of it is finite. Finiteness of `H` is what an
infinite extension `M / K` can still supply. -/
theorem fixingSubgroup_fixedField_of_finite (H : Subgroup (M ≃ₐ[K] M)) [Finite H] :
    fixingSubgroup (fixedField H) = H := by
  refine le_antisymm (fun σ hσ ↦ ?_) ((le_iff_le _ _).mp le_rfl)
  rw [mem_fixingSubgroup_iff] at hσ
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective H M
    (AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x ↦ hσ x x.2)
  have hgσ : (g : M ≃ₐ[K] M) = σ := AlgEquiv.ext fun z ↦ congrArg (fun τ ↦ τ z) hg
  exact hgσ ▸ g.2

/-- **An intermediate field of finite degree has a finite fixing subgroup**, being a copy of the
automorphism group of a finite extension. -/
instance finite_fixingSubgroup (E : IntermediateField K M) [FiniteDimensional E M] :
    Finite (fixingSubgroup E) :=
  .of_equiv _ (fixingSubgroupEquiv E).symm.toEquiv

/-- **A group of automorphisms whose fixed field has finite degree is finite.** Thus a subgroup of
`K`-automorphisms cannot be infinite when its fixed field has finite degree in `M`. -/
theorem finite_of_finiteDimensional_fixedField (H : Subgroup (M ≃ₐ[K] M))
    [FiniteDimensional (fixedField H) M] : Finite H :=
  letI := finite_fixingSubgroup (fixedField H)
  have hH : H ≤ fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  .of_injective (Set.inclusion hH) (Set.inclusion_injective hH)

/-- **The fixing subgroup of an intermediate field of finite degree is no larger than that
degree**, the bound on the automorphisms of a finite extension. -/
theorem card_fixingSubgroup_le (E : IntermediateField K M) [FiniteDimensional E M] :
    Nat.card (fixingSubgroup E) ≤ Module.finrank E M := by
  rw [Nat.card_congr (fixingSubgroupEquiv E).toEquiv, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

/-- **The fixing subgroup of a simple extension is the stabilizer of its generator.** A
`K`-automorphism of `M` is determined on `K⟮x⟯` by its value at `x`, so fixing `K⟮x⟯` pointwise is
fixing `x`; no hypothesis on `M / K` is needed, and `x` need not be algebraic.

This is what turns a statement about the action of `Gal(M/K)` on a set of elements of `M` into a
statement about the Galois correspondence. -/
@[simp]
theorem fixingSubgroup_adjoin_simple (x : M) :
    K⟮x⟯.fixingSubgroup = MulAction.stabilizer (M ≃ₐ[K] M) x := by
  ext σ
  rw [mem_fixingSubgroup_iff, MulAction.mem_stabilizer_iff]
  simpa using forall_mem_adjoin_smul_eq_self_iff K (S := {x}) σ

end IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- **The Galois correspondence is conjugation-equivariant.** The fixed field of the conjugate
subgroup `σ H σ⁻¹` is the image under `σ` of the fixed field of `H`.

Stated in the `Subgroup` namespace, so that `H` — the first explicit argument, and the one
`fixedField` is applied to — carries the dot notation. -/
@[simp]
theorem fixedField_map_conj (H : Subgroup (M ≃ₐ[K] M)) (σ : M ≃ₐ[K] M) :
    fixedField (H.map (MulAut.conj σ)) = (fixedField H).map σ.toAlgHom := by
  ext x
  simp only [mem_fixedField_iff, IntermediateField.mem_map]
  constructor
  · intro h
    refine ⟨σ.symm x, fun g hg ↦ ?_, by simp⟩
    have hx := h (MulAut.conj σ g) (Subgroup.mem_map_of_mem _ hg)
    simpa [MulAut.conj_apply] using congrArg σ.symm hx
  · rintro ⟨y, hy, rfl⟩ g ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply] using congrArg σ (hy h hh)

end Subgroup

namespace FixedPoints

/-- **The fixed subfield of a finite cyclic group action has cyclic Galois group.** For a finite
cyclic group `G` acting on a field `F` by ring automorphisms, `F` is cyclic over its subfield of
`G`-fixed points.

No faithfulness is asked of the action: `FixedPoints.toAlgAut_surjective` needs only finiteness,
and cyclicity passes along any surjection. A non-faithful action simply presents the Galois group
as a proper quotient of `G`, which is cyclic all the same. -/
theorem isCyclic_algEquiv (G F : Type*) [Group G] [Field F] [MulSemiringAction G F] [Finite G]
    [IsCyclic G] : IsCyclic (F ≃ₐ[FixedPoints.subfield G F] F) :=
  isCyclic_of_surjective _ (FixedPoints.toAlgAut_surjective G F)

end FixedPoints

namespace AlgEquiv

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

-- Source. The fixed field of `⟨σ⟩` and its named generator are the constructions pinned at
-- `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 283-291, as `cyclicFixedField` and
-- `fixedFieldGenerator`. Neither name is kept: the field is spelled
-- `IntermediateField.fixedField (Subgroup.zpowers σ)` throughout rather than abbreviated, and the
-- automorphism is `toFixedFieldAlgEquiv`, because it is defined without finiteness and only
-- generates once `⟨σ⟩` is finite.

/-- **The automorphism of `M` over `M ^ ⟨σ⟩` given by `σ`.** Acting through `⟨σ⟩` fixes
`M ^ ⟨σ⟩` pointwise, so `σ` is an automorphism over that field; this is that automorphism, and
nothing more. It is `σ` rebundled over a smaller base, so the name says only that.

Named rather than inlined so that consumers have a term to talk about: a fibre count needs the
relative Frobenius exhibited as a specific power of a specific generator, and `IsCyclic` supplies
only an anonymous one. Use `toFixedFieldAlgEquiv_apply` to compute with it. That it *generates* is
`zpowers_toFixedFieldAlgEquiv_eq_top`, a separate statement, and it is the only one that needs
`⟨σ⟩` to be finite. -/
def toFixedFieldAlgEquiv (σ : M ≃ₐ[K] M) :
    M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] M :=
  MulSemiringAction.toAlgAut (Subgroup.zpowers σ)
    (FixedPoints.subfield (Subgroup.zpowers σ) M) M ⟨σ, Subgroup.mem_zpowers σ⟩

/-- **The rebundled automorphism acts as `σ`.** This is what makes `toFixedFieldAlgEquiv σ`
usable: it is a different bundling of the same underlying map, over the fixed field rather than
over `K`. It says nothing about generation, which needs `⟨σ⟩` finite and is
`zpowers_toFixedFieldAlgEquiv_eq_top`. -/
@[simp]
theorem toFixedFieldAlgEquiv_apply (σ : M ≃ₐ[K] M) (x : M) :
    toFixedFieldAlgEquiv σ x = σ x :=
  (rfl)

/-- **Restricting scalars undoes the rebundling.** Read back over `K`, `σ.toFixedFieldAlgEquiv`
is `σ` itself — the elimination rule matching `toFixedFieldAlgEquiv_apply`, in bundled form, which
is what a tower argument needs when it must produce an equation between automorphisms rather than
between their values. -/
@[simp]
theorem restrictScalars_toFixedFieldAlgEquiv (σ : M ≃ₐ[K] M) :
    AlgEquiv.restrictScalars K σ.toFixedFieldAlgEquiv = σ :=
  AlgEquiv.ext fun x ↦ toFixedFieldAlgEquiv_apply σ x

/-- **And, for finite `⟨σ⟩`, it generates.** The automorphisms of `M` fixing `M ^ ⟨σ⟩` are exactly
the powers of `σ.toFixedFieldAlgEquiv`.

Together with `FixedPoints.isCyclic_algEquiv`, applied to the action of `⟨σ⟩` on `M`, this is the
cyclic picture of `M / M ^ ⟨σ⟩` with a named generator; neither statement asks `M / K` to be
finite or Galois. -/
@[simp]
theorem zpowers_toFixedFieldAlgEquiv_eq_top (σ : M ≃ₐ[K] M) [Finite (Subgroup.zpowers σ)] :
    Subgroup.zpowers (toFixedFieldAlgEquiv σ) = ⊤ := by
  -- Generation is a statement about the `MulEquiv`, so it is proved for `toAlgAutMulEquiv` and
  -- then transported to `toFixedFieldAlgEquiv` by `exact`, which works up to definitional equality:
  -- `toAlgAutMulEquiv` is `MulEquiv.ofBijective` of the very `toAlgAut` the definition uses. It
  -- cannot be done by rewriting with `toFixedFieldAlgEquiv` instead, because that term lives over
  -- `FixedPoints.subfield`, defeq to `IntermediateField.fixedField` but not syntactically equal,
  -- so `rw` produces a type-incorrect goal.
  --
  -- Within the `have`, `MonoidHom.map_zpowers` is about a `MonoidHom`, so the `MulEquiv`
  -- application is restated through `MulEquiv.coe_toMonoidHom` rather than by unfolding the
  -- coercion. The image of `⊤` is then `Subgroup.map_equiv_top`, which `simp` reaches through
  -- `MulEquiv.toMonoidHom_eq_coe`.
  have h : Subgroup.zpowers (FixedPoints.toAlgAutMulEquiv (Subgroup.zpowers σ) M
      ⟨σ, Subgroup.mem_zpowers σ⟩) = ⊤ := by
    rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_zpowers, Subgroup.zpowers_mk_self_eq_top]
    simp
  exact h

end AlgEquiv
