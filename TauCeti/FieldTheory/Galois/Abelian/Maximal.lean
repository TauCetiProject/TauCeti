/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Abelian.Basic
public import TauCeti.FieldTheory.Galois.Quotient

/-!
# The maximal abelian extension

For an extension `Ω/K`, the **maximal abelian extension** `K^{ab}` of `K` in `Ω` is the compositum
of all intermediate fields `E` of `Ω/K` that are abelian Galois over `K`. It is itself abelian
Galois over `K`, so it is the largest such intermediate field: an intermediate field lies in
`K^{ab}` exactly when it is abelian Galois over `K`.

When `Ω/K` is normal, for instance when `Ω` is an algebraic closure of `K`, the Galois
correspondence identifies `K^{ab}` with the closed commutator subgroup of `Gal(Ω/K)`: the fixing
subgroup of `K^{ab}` is the topological closure of `[Gal(Ω/K), Gal(Ω/K)]`. Consequently the
topological abelianization `Gal(Ω/K)^{ab} = Gal(Ω/K) ⧸ closure [Gal(Ω/K), Gal(Ω/K)]` is the Galois
group `Gal(K^{ab}/K)`, as a topological group. For `Ω = AlgebraicClosure K` this exhibits Mathlib's
`Field.absoluteGaloisGroupAbelianization K` as the Galois group of an intermediate field of the
algebraic closure, the target of the reciprocity maps of class field theory.

The commutator subgroup cuts out a field inside the separable closure only: in positive
characteristic the fixed field of the closed commutator subgroup also contains the purely
inseparable elements of `Ω`, which are fixed by every automorphism. This is why `K^{ab}` is
defined as a compositum of Galois extensions rather than as a fixed field; it always lies in the
separable closure of `K` in `Ω`.

## Main definitions

* `TauCeti.maximalAbelianExtension K Ω`: the compositum of the abelian Galois subextensions of
  `Ω/K`.
* `TauCeti.topologicalAbelianizationEquivMaximalAbelianExtension`: for `Ω/K` normal, the
  isomorphism of topological groups `Gal(Ω/K)^{ab} ≃ₜ* Gal(K^{ab}/K)` induced by restriction.

## Main results

* `TauCeti.isAbelianGalois_maximalAbelianExtension`: `K^{ab}/K` is abelian Galois.
* `TauCeti.le_maximalAbelianExtension_iff`: an intermediate field lies in `K^{ab}` exactly when
  it is abelian Galois over `K`.
* `TauCeti.mem_maximalAbelianExtension_iff`: an element lies in `K^{ab}` exactly when it lies in
  some abelian Galois subextension.
* `TauCeti.maximalAbelianExtension_le_separableClosure`: `K^{ab}` lies in the separable closure.
* `TauCeti.isAbelianGalois_fixedField_inf_separableClosure`: for `Ω/K` normal, the separable part
  of the fixed field of the closed commutator subgroup of `Gal(Ω/K)` is abelian Galois over `K`.
* `TauCeti.fixingSubgroup_maximalAbelianExtension`: for `Ω/K` normal, the fixing subgroup of
  `K^{ab}` is the closed commutator subgroup of `Gal(Ω/K)`.
* `TauCeti.maximalAbelianExtension_eq_fixedField_inf_separableClosure`: for `Ω/K` normal,
  `K^{ab}` is the separable part of the fixed field of that subgroup.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §1 and
  Ch. VI §1, for the Galois correspondence over an infinite extension.
* J. S. Milne, *Fields and Galois Theory*, Ch. 7, for Krull's correspondence between closed
  normal subgroups and Galois subextensions.
-/

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- The **maximal abelian extension** `K^{ab}` of `K` in `Ω`: the compositum of all intermediate
fields of `Ω/K` that are abelian Galois over `K`. -/
def maximalAbelianExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsAbelianGalois K E}, (E : IntermediateField K Ω)

/-- The maximal abelian extension is the compositum of the abelian Galois subextensions. -/
theorem maximalAbelianExtension_def :
    maximalAbelianExtension K Ω =
      ⨆ E : {E : IntermediateField K Ω // IsAbelianGalois K E}, (E : IntermediateField K Ω) :=
  -- `(rfl)`, not `rfl`: keep the body opaque while exporting this equation across modules.
  (rfl)

variable {K Ω}

/-- Every abelian Galois subextension lies in the maximal abelian extension. -/
theorem _root_.IntermediateField.le_maximalAbelianExtension (E : IntermediateField K Ω)
    [IsAbelianGalois K E] : E ≤ maximalAbelianExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsAbelianGalois K E} ↦ (E : IntermediateField K Ω))
    ⟨E, ‹_›⟩

variable (K Ω) in
/-- **The maximal abelian extension is abelian Galois.** -/
instance isAbelianGalois_maximalAbelianExtension :
    IsAbelianGalois K (maximalAbelianExtension K Ω) := by
  have : ∀ E : {E : IntermediateField K Ω // IsAbelianGalois K E},
      IsAbelianGalois K (E : IntermediateField K Ω) := fun E ↦ E.2
  rw [maximalAbelianExtension_def]
  infer_instance

/-- **The maximal abelian extension is the largest abelian Galois subextension**: an intermediate
field lies in it exactly when it is abelian Galois over `K`. -/
theorem le_maximalAbelianExtension_iff {E : IntermediateField K Ω} :
    E ≤ maximalAbelianExtension K Ω ↔ IsAbelianGalois K E :=
  ⟨fun h ↦ .of_algHom (IntermediateField.inclusion h), fun _ ↦ le_maximalAbelianExtension E⟩

/-- An element lies in the maximal abelian extension exactly when it lies in some intermediate
field that is abelian Galois over `K`. -/
theorem mem_maximalAbelianExtension_iff {x : Ω} :
    x ∈ maximalAbelianExtension K Ω ↔ ∃ E : IntermediateField K Ω, IsAbelianGalois K E ∧ x ∈ E :=
  ⟨fun hx ↦ ⟨_, inferInstance, hx⟩, fun ⟨E, _, hx⟩ ↦ le_maximalAbelianExtension E hx⟩

variable (K Ω) in
/-- The maximal abelian extension lies in the separable closure of `K` in `Ω`. -/
theorem maximalAbelianExtension_le_separableClosure :
    maximalAbelianExtension K Ω ≤ separableClosure K Ω :=
  le_separableClosure K Ω _

/-! ### The Galois correspondence for the maximal abelian extension -/

section Normal

variable [Normal K Ω]

variable (K Ω) in
/-- The separable part of the fixed field of the closed commutator subgroup of `Gal(Ω/K)` is an
abelian Galois extension of `K`. -/
theorem isAbelianGalois_fixedField_inf_separableClosure :
    IsAbelianGalois K ↥(fixedField (commutator Gal(Ω/K)).topologicalClosure ⊓
      separableClosure K Ω) := by
  set C := (commutator Gal(Ω/K)).topologicalClosure
  set M := fixedField C ⊓ separableClosure K Ω
  -- `M` is normal because the closed commutator subgroup is a normal subgroup, and abelian
  -- because restricting to it kills every commutator.
  have : Algebra.IsSeparable K M := (le_separableClosure_iff K Ω M).mp inf_le_right
  have : Normal K M := by
    refine normal_iff_forall_map_le'.mpr fun σ y hy ↦ ?_
    obtain ⟨x, hx, rfl⟩ := (mem_map (S := M)).mp hy
    obtain ⟨hxC, hxS⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨(mem_fixedField_iff _ _).mpr fun c hc ↦ ?_, ?_⟩
    · -- `σ⁻¹ c σ` lies in the normal subgroup `C`, so it fixes `x`.
      have hfix := (mem_fixedField_iff _ _).mp hxC _
        ((inferInstance : C.Normal).conj_mem c hc σ⁻¹)
      simpa only [inv_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply,
        AlgEquiv.symm_symm, AlgEquiv.coe_toAlgHom] using congrArg σ hfix
    · exact (map_mem_separableClosure_iff (σ : Ω →ₐ[K] Ω)).mpr hxS
  have : IsGalois K M := ⟨⟩
  have hker : C ≤ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M).ker := by
    rw [IntermediateField.restrictNormalHom_ker, fixingSubgroup_inf_separableClosure,
      fixingSubgroup_fixedField (Subgroup.isClosed_topologicalClosure _)]
  refine { is_comm := ⟨fun a b ↦ ?_⟩ }
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω a
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective Ω b
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact hker (Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top σ) (Subgroup.mem_top τ)))

variable (K Ω) in
/-- **The maximal abelian extension corresponds to the closed commutator subgroup**: for `Ω/K`
normal, the subgroup of `Gal(Ω/K)` fixing `K^{ab}` is the topological closure of the commutator
subgroup. -/
theorem fixingSubgroup_maximalAbelianExtension :
    (maximalAbelianExtension K Ω).fixingSubgroup = (commutator Gal(Ω/K)).topologicalClosure := by
  set C := (commutator Gal(Ω/K)).topologicalClosure
  refine le_antisymm ?_ ?_
  · -- The separable part of the fixed field of `C` is abelian Galois, hence lies in `K^{ab}`.
    have := isAbelianGalois_fixedField_inf_separableClosure K Ω
    calc (maximalAbelianExtension K Ω).fixingSubgroup
        ≤ (fixedField C ⊓ separableClosure K Ω).fixingSubgroup :=
          fixingSubgroup_antitone (le_maximalAbelianExtension _)
      _ = C := by
          rw [fixingSubgroup_inf_separableClosure,
            fixingSubgroup_fixedField (Subgroup.isClosed_topologicalClosure _)]
  · -- Restriction to `K^{ab}` lands in a commutative group, so its kernel, a closed subgroup,
    -- contains every commutator.
    refine (commutator Gal(Ω/K)).topologicalClosure_minimal ?_
      (fixingSubgroup_isClosed_of_isAlgebraic _)
    rw [← IntermediateField.restrictNormalHom_ker]
    exact Abelianization.commutator_le_ker _

variable (K Ω) in
/-- **The maximal abelian extension is the separable part of the fixed field of the closed
commutator subgroup**, for `Ω/K` normal. The intersection with the separable closure cannot be
dropped in positive characteristic, where the fixed field also contains the purely inseparable
closure of `K` in `Ω`. -/
theorem maximalAbelianExtension_eq_fixedField_inf_separableClosure :
    maximalAbelianExtension K Ω =
      fixedField (commutator Gal(Ω/K)).topologicalClosure ⊓ separableClosure K Ω := by
  have := isAbelianGalois_fixedField_inf_separableClosure K Ω
  refine le_antisymm (le_inf ?_ (maximalAbelianExtension_le_separableClosure K Ω))
    (le_maximalAbelianExtension _)
  rw [le_fixedField_iff_le_fixingSubgroup, fixingSubgroup_maximalAbelianExtension]

variable (K Ω) in
/-- **The Galois group of the maximal abelian extension is the topological abelianization**: for
`Ω/K` normal, restriction to `K^{ab}` induces an isomorphism of topological groups
`Gal(Ω/K) ⧸ closure [Gal(Ω/K), Gal(Ω/K)] ≃ₜ* Gal(K^{ab}/K)`. -/
def topologicalAbelianizationEquivMaximalAbelianExtension :
    TopologicalAbelianization Gal(Ω/K) ≃ₜ* Gal(maximalAbelianExtension K Ω/K) :=
  ((ContinuousMulEquiv.refl Gal(Ω/K)).quotientCongr _ _ (by
      rw [fixingSubgroup_maximalAbelianExtension]
      exact Subgroup.map_id _)).trans
    (quotientFixingSubgroupEquiv K Ω (maximalAbelianExtension K Ω))

/-- The isomorphism `Gal(Ω/K)^{ab} ≃ₜ* Gal(K^{ab}/K)` sends the class of `σ` to its restriction to
`K^{ab}`. -/
@[simp]
theorem _root_.AlgEquiv.topologicalAbelianizationEquivMaximalAbelianExtension_mk
    (σ : Gal(Ω/K)) :
    topologicalAbelianizationEquivMaximalAbelianExtension K Ω (σ : TopologicalAbelianization _) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) σ := by
  rw [topologicalAbelianizationEquivMaximalAbelianExtension, ContinuousMulEquiv.trans_apply,
    ContinuousMulEquiv.quotientCongr_mk, ContinuousMulEquiv.refl_apply,
    quotientFixingSubgroupEquiv_mk]

/-- The inverse isomorphism `Gal(K^{ab}/K) ≃ₜ* Gal(Ω/K)^{ab}` sends the restriction of `σ` to
`K^{ab}` back to the class of `σ`; with `AlgEquiv.restrictNormalHom_surjective` this computes it
on every element. -/
@[simp]
theorem _root_.AlgEquiv.topologicalAbelianizationEquivMaximalAbelianExtension_symm_restrictNormalHom
    (σ : Gal(Ω/K)) :
    (topologicalAbelianizationEquivMaximalAbelianExtension K Ω).symm
        (AlgEquiv.restrictNormalHom (maximalAbelianExtension K Ω) σ) =
      (σ : TopologicalAbelianization _) := by
  rw [ContinuousMulEquiv.symm_apply_eq,
    AlgEquiv.topologicalAbelianizationEquivMaximalAbelianExtension_mk]

end Normal

end TauCeti
