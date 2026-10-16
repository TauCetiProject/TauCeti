/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.Relrank

/-!
# Relative degrees under linearly disjoint base change

If `A` is algebraic over `k` and linearly disjoint from `B` over `k`, adjoining `A` preserves the
relative degree of an intermediate extension `B/C`. This is the field-tower calculation behind
the degree comparison for algebraic function fields after extending their constants, where `A`
is a constant field extension, finite or not, for instance an algebraic closure.

The proof shows that a family in `B` linearly independent over `C` stays linearly independent over
`A ⊔ C`. Every element of `A ⊔ C` is an `A`-linear combination of a `k`-basis `γ` of `C`, because
the compositum with an algebraic extension is the ring it generates; and for a `C`-basis `β` of
`B` the products `γ m * β i` form a `k`-basis of `B`, which linear disjointness keeps linearly
independent over `A`.

## Main results

* `IntermediateField.coe_sup_eq_span_of_isAlgebraic_left`: for `A` algebraic, `A ⊔ D` is the
  `A`-span of `D`.
* `TauCeti.linearIndependent_of_linearIndependent_mul_of_mem_span`: if a family `γ` spans `S` over
  `R` and the products `γ m * β i` are linearly independent over `R`, then `β` is linearly
  independent over `S`.
* `IntermediateField.LinearDisjoint.linearIndependent_sup_of_isAlgebraic_left`: linear
  independence over `C ≤ B` persists over `A ⊔ C`.
* `IntermediateField.relrank_sup_sup_eq_relrank_of_linearDisjoint` and
  `IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint`:
  `[A ⊔ B : A ⊔ C] = [B : C]`. Apply them as
  `A.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint B C hCB h`, where `hCB : C ≤ B` and
  `h : A.LinearDisjoint B`; the algebraicity of `A` is supplied by an instance.
* `IntermediateField.relrank_eq_relrank_of_toSubfield_eq` and
  `IntermediateField.relfinrank_eq_relfinrank_of_toSubfield_eq`: relative degrees depend only on
  the underlying subfields, so they can be compared across base fields.

The declarations live in Mathlib's `IntermediateField` namespace so that this dot notation works.

`IntermediateField.LinearDisjoint.linearIndependent_algebraMap_comp` extends scalars on the other
side: if the image of `k'` in a common overfield `E` is linearly disjoint from `F` over `k`, a
family of `F` linearly independent over `k` stays linearly independent over `k'` in `E`.
`TauCeti.linearDisjoint_fieldRange_of_forall_finiteDimensional` reduces that linear disjointness,
for algebraic `k' / k`, to the finite subextensions of `k' / k`.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

/-- Extending scalars from `D` to its compositum with `A` amounts to adjoining `A` to `D`. -/
theorem _root_.IntermediateField.extendScalars_sup_right_eq_adjoin (A D : IntermediateField k L) :
    IntermediateField.extendScalars (le_sup_right : D ≤ A ⊔ D) =
      IntermediateField.adjoin D (A : Set L) := by
  apply IntermediateField.restrictScalars_injective k
  rw [IntermediateField.extendScalars_restrictScalars,
    IntermediateField.restrictScalars_adjoin_eq_sup, sup_comm,
    IntermediateField.adjoin_self]

/-- An algebraic extension linearly disjoint from `D` has the same degree after adjoining `D`. -/
theorem _root_.IntermediateField.relfinrank_sup_right_eq_finrank_of_linearDisjoint
    (A D : IntermediateField k L) [Algebra.IsAlgebraic k A] (hAD : A.LinearDisjoint D) :
    IntermediateField.relfinrank D (A ⊔ D) =
      Module.finrank k A := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_sup_right : D ≤ A ⊔ D),
    IntermediateField.extendScalars_sup_right_eq_adjoin]
  exact congrArg Cardinal.toNat hAD.adjoin_rank_eq_rank_left_of_isAlgebraic_left

/-- **The compositum with an algebraic extension is a span.** If `A` is algebraic over `k`, the
compositum `A ⊔ D` is the `A`-span of `D`: it is the ring `A[D]`, and `D` is closed under
multiplication. -/
theorem _root_.IntermediateField.coe_sup_eq_span_of_isAlgebraic_left (A D : IntermediateField k L)
    [Algebra.IsAlgebraic k A] :
    ((A ⊔ D : IntermediateField k L) : Set L) = Submodule.span A (D : Set L) := by
  have hclosure : (Submonoid.closure (D : Set L) : Set L) ⊆ Submodule.span A (D : Set L) :=
    fun _ hy ↦ Submodule.subset_span
      ((Submonoid.closure_le (S := D.toSubalgebra.toSubmonoid)).mpr subset_rfl hy)
  rw [← IntermediateField.adjoin_self k D, ← IntermediateField.restrictScalars_adjoin_eq_sup,
    IntermediateField.adjoin_self, IntermediateField.coe_restrictScalars,
    ← IntermediateField.coe_toSubalgebra,
    IntermediateField.adjoin_intermediateField_toSubalgebra_of_isAlgebraic_left,
    ← Subalgebra.coe_toSubmodule, Algebra.adjoin_eq_span_of_subset A hclosure]

/-- A span over an intermediate field lies in the span over any larger intermediate field. -/
theorem _root_.IntermediateField.span_subset_span_of_le {S S' : IntermediateField k L}
    (h : S ≤ S') (t : Set L) : (Submodule.span S t : Set L) ⊆ Submodule.span S' t :=
  letI : Algebra S S' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower S S' L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Submodule.span_subset_span S S' t

/-- **Linear independence over a field spanned by a family.** If every element of `S` is an
`R`-linear combination of a family `γ` in `L`, and the products `γ m * β i` are linearly
independent over `R`, then `β` is linearly independent over `S`. -/
theorem linearIndependent_of_linearIndependent_mul_of_mem_span {R S : Type*} [CommRing R]
    [Field S] [Algebra R L] [Algebra S L] {κ ι : Type*} {γ : κ → L} {β : ι → L}
    (hγ : ∀ x : S, algebraMap S L x ∈ Submodule.span R (Set.range γ))
    (h : LinearIndependent R fun p : ι × κ ↦ γ p.2 * β p.1) :
    LinearIndependent S β := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose c hc using fun j ↦ (Finsupp.mem_span_range_iff_exists_finsupp).mp (hγ (g j))
  let T := s.biUnion fun j ↦ (c j).support
  have hgT : ∀ j ∈ s, algebraMap S L (g j) = ∑ m ∈ T, c j m • γ m := fun j hj ↦ by
    rw [← hc j, Finsupp.sum_of_support_subset _
      (Finset.subset_biUnion_of_mem (fun j ↦ (c j).support) hj)]
    intro m _
    simp
  have hzero : ∑ p ∈ s ×ˢ T, c p.1 p.2 • (γ p.2 * β p.1) = 0 := by
    rw [Finset.sum_product, ← hg]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Algebra.smul_def, hgT j hj, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ ↦ (smul_mul_assoc _ _ _).symm
  have hc0 := (linearIndependent_iff'.mp h) (s ×ˢ T) (fun p ↦ c p.1 p.2) hzero
  refine (algebraMap S L).injective ?_
  rw [hgT i hi, map_zero]
  exact Finset.sum_eq_zero fun m hm ↦ by
    rw [hc0 (i, m) (Finset.mem_product.mpr ⟨hi, hm⟩), zero_smul]

/-- **Linear disjointness survives adjoining part of the other side.** Let `A` be algebraic over
`k` and linearly disjoint from `B`, and let `C ≤ B`. A family in `B` that is linearly
independent over `C` stays linearly independent over the compositum `A ⊔ C`. -/
theorem _root_.IntermediateField.LinearDisjoint.linearIndependent_sup_of_isAlgebraic_left
    {A B C : IntermediateField k L} [Algebra.IsAlgebraic k A] (h : A.LinearDisjoint B)
    (hCB : C ≤ B) {ι : Type*} {β : ι → L} (hβB : ∀ i, β i ∈ B) (hβ : LinearIndependent C β) :
    LinearIndependent (A ⊔ C : IntermediateField k L) β := by
  classical
  let γ := Module.Basis.ofVectorSpace k C
  let γ' : _ → L := fun m ↦ (γ m : L)
  -- the products `γ m * β i` are linearly independent over `k`, hence over `A`
  have hprod : LinearIndependent A fun p : ι × _ ↦ γ' p.2 * β p.1 := by
    have hk : LinearIndependent k fun p : _ × ι ↦ γ p.1 • β p.2 :=
      linearIndependent_smul γ.linearIndependent hβ
    have hkB : LinearIndependent k fun p : _ × ι ↦
        (⟨γ p.1 • β p.2, B.mul_mem (hCB (γ p.1).2) (hβB p.2)⟩ : B) :=
      .of_comp B.val.toLinearMap hk
    have hA := h.linearIndependent_right hkB
    exact (hA.comp (Equiv.prodComm _ _) (Equiv.injective _))
  -- every element of `A ⊔ C` is an `A`-combination of the `γ m`
  refine linearIndependent_of_linearIndependent_mul_of_mem_span (fun x ↦ ?_) hprod
  have hC : (C : Set L) ⊆ Submodule.span A (Set.range γ') := by
    intro c hc
    have hck : c ∈ Submodule.span k (Set.range γ') := by
      have hmem := γ.mem_span (⟨c, hc⟩ : C)
      have := Submodule.mem_map_of_mem (f := C.val.toLinearMap) hmem
      rwa [Submodule.map_span, ← Set.range_comp] at this
    exact Submodule.span_le_restrictScalars k A _ hck
  have hx : (x : L) ∈ ((A ⊔ C : IntermediateField k L) : Set L) := x.2
  rw [IntermediateField.coe_sup_eq_span_of_isAlgebraic_left] at hx
  exact Submodule.span_le.mpr hC hx

/-- **Base change by an algebraic linearly disjoint extension preserves relative degrees.** If `A`
is algebraic over `k` and linearly disjoint from `B`, then adjoining `A` does not change the
relative degree of an intermediate extension `B / C`: `[A ⊔ B : A ⊔ C] = [B : C]`, as cardinals. -/
theorem _root_.IntermediateField.relrank_sup_sup_eq_relrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B) [Algebra.IsAlgebraic k A]
    (h : A.LinearDisjoint B) :
    IntermediateField.relrank (A ⊔ C) (A ⊔ B) = IntermediateField.relrank C B := by
  have hle : A ⊔ C ≤ A ⊔ B := sup_le_sup_left hCB A
  let β₀ := Module.Basis.ofVectorSpace C (IntermediateField.extendScalars hCB)
  let β : _ → L := fun i ↦ (β₀ i : L)
  have hβB : ∀ i, β i ∈ B := fun i ↦ (β₀ i).2
  have hβ : LinearIndependent C β :=
    β₀.linearIndependent.map' (IntermediateField.extendScalars hCB).val.toLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hβ' := h.linearIndependent_sup_of_isAlgebraic_left hCB hβB hβ
  -- `A ⊔ B` is spanned over `A ⊔ C` by the basis `β` of `B / C`
  have hspan : Subalgebra.toSubmodule (IntermediateField.extendScalars hle).toSubalgebra =
      Submodule.span (A ⊔ C : IntermediateField k L) (Set.range β) := by
    refine le_antisymm (fun x hx ↦ ?_) (Submodule.span_le.mpr ?_)
    · have hB : (B : Set L) ⊆ Submodule.span (A ⊔ C : IntermediateField k L) (Set.range β) := by
        intro b hb
        have hmem := β₀.mem_span (⟨b, hb⟩ : IntermediateField.extendScalars hCB)
        have := Submodule.mem_map_of_mem
          (f := (IntermediateField.extendScalars hCB).val.toLinearMap) hmem
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact IntermediateField.span_subset_span_of_le le_sup_right _ this
      have hAB : x ∈ Submodule.span A (B : Set L) := by
        rw [← SetLike.mem_coe, ← IntermediateField.coe_sup_eq_span_of_isAlgebraic_left]
        exact hx
      exact Submodule.span_le.mpr hB (IntermediateField.span_subset_span_of_le le_sup_left _ hAB)
    · rintro _ ⟨i, rfl⟩
      exact le_sup_right (a := A) (hβB i)
  rw [IntermediateField.relrank_eq_rank_of_le hle, IntermediateField.relrank_eq_rank_of_le hCB,
    ← IntermediateField.rank_eq_rank_subalgebra, ← Subalgebra.rank_toSubmodule, hspan,
    rank_span hβ', ← β₀.mk_eq_rank'', Cardinal.mk_range_eq _ hβ'.injective]

/-- Base change by an algebraic linearly disjoint extension preserves the degree of an intermediate
field extension. -/
theorem _root_.IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B)
    [Algebra.IsAlgebraic k A] (h : A.LinearDisjoint B) :
    IntermediateField.relfinrank (A ⊔ C) (A ⊔ B) =
      IntermediateField.relfinrank C B :=
  congrArg Cardinal.toNat (A.relrank_sup_sup_eq_relrank_of_linearDisjoint B C hCB h)

/-- The relative degree of intermediate fields depends only on their underlying subfields, so it
can be compared across different base fields. -/
theorem _root_.IntermediateField.relrank_eq_relrank_of_toSubfield_eq {k' : Type*} [Field k']
    [Algebra k' L] {A B : IntermediateField k L} {A' B' : IntermediateField k' L}
    (hA : A.toSubfield = A'.toSubfield) (hB : B.toSubfield = B'.toSubfield) :
    IntermediateField.relrank A B = IntermediateField.relrank A' B' :=
  congrArg₂ Subfield.relrank hA hB

/-- The relative degree of intermediate fields depends only on their underlying subfields, so it
can be compared across different base fields. -/
theorem _root_.IntermediateField.relfinrank_eq_relfinrank_of_toSubfield_eq {k' : Type*}
    [Field k'] [Algebra k' L] {A B : IntermediateField k L} {A' B' : IntermediateField k' L}
    (hA : A.toSubfield = A'.toSubfield) (hB : B.toSubfield = B'.toSubfield) :
    IntermediateField.relfinrank A B = IntermediateField.relfinrank A' B' :=
  congrArg Cardinal.toNat (IntermediateField.relrank_eq_relrank_of_toSubfield_eq hA hB)

section ExtendScalars

variable {k' : Type*} {F : Type*} {E : Type*} [Field k'] [Field F] [Field E]
variable [Algebra k k'] [Algebra k F] [Algebra k E] [Algebra k' E] [Algebra F E]
variable [IsScalarTower k k' E] [IsScalarTower k F E]

/-- **Linear independence over `k` persists over `k'` under linear disjointness**: if the image of
`k'` in `E` and `F` are linearly disjoint over `k`, then a family of elements of `F` linearly
independent over `k` stays linearly independent over `k'` inside `E`. -/
theorem _root_.IntermediateField.LinearDisjoint.linearIndependent_algebraMap_comp
    (H : (IsScalarTower.toAlgHom k k' E).fieldRange.LinearDisjoint F) {ι : Type*} {v : ι → F}
    (hv : LinearIndependent k v) : LinearIndependent k' (algebraMap F E ∘ v) :=
  (H.linearIndependent_right' hv).map_of_injective_injective
    (IsScalarTower.toAlgHom k k' E).equivFieldRange (AddMonoidHom.id E) (by simp) (by simp)
    fun _ _ ↦ by
      simp only [AddMonoidHom.id_apply, Algebra.smul_def, IntermediateField.algebraMap_apply,
        AlgHom.equivFieldRange_apply_coe, IsScalarTower.toAlgHom_apply]

/-- **Linear disjointness from the finite subextensions**: if `k' / k` is algebraic and the image
in `E` of every finite subextension `M` of `k' / k` is linearly disjoint from `F` over `k`, then so
is the image of `k'`.  Finitely many elements of `k'` lie in a finite subextension. -/
theorem linearDisjoint_fieldRange_of_forall_finiteDimensional [Algebra.IsAlgebraic k k']
    (h : ∀ M : IntermediateField k k', FiniteDimensional k M →
      (IsScalarTower.toAlgHom k M E).fieldRange.LinearDisjoint F) :
    (IsScalarTower.toAlgHom k k' E).fieldRange.LinearDisjoint F := by
  let f := IsScalarTower.toAlgHom k k' E
  have : Algebra.IsAlgebraic k f.fieldRange := f.equivFieldRange.isAlgebraic
  rw [IntermediateField.linearDisjoint_iff]
  apply Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left
  intro A hA hfinite
  let N : IntermediateField k E := Algebra.IsAlgebraic.toIntermediateField A
  let M : IntermediateField k k' := N.comap f
  let g : M →ₐ[k] A := (f.comp M.val).codRestrict A fun x => x.property
  have : FiniteDimensional k M :=
    FiniteDimensional.of_injective g.toLinearMap g.injective
  have hN : N ≤ f.fieldRange := hA
  have hmap : M.map f = N := IntermediateField.map_comap_eq_self hN
  have hfield : (IsScalarTower.toAlgHom k M E).fieldRange = N := by
    -- The tower map through M is definitionally the restriction f.comp M.val.
    -- Expose that restriction to apply the field-range/map identity.
    change (f.comp M.val).fieldRange = N
    rw [IntermediateField.fieldRange_comp_val, hmap]
  have hdisj := h M this
  rw [IntermediateField.linearDisjoint_iff, hfield] at hdisj
  exact hdisj

end ExtendScalars

end TauCeti
