/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic

/-!
# A number field is discrete in its adele ring

Let `K` be a number field with adele ring `𝔸[K] = K∞ × 𝔸ᶠ[K]`.  The diagonal copy of `K`, which is
Mathlib's `NumberField.AdeleRing.principalSubgroup (𝓞 K) K`, is a discrete and closed additive
subgroup of `𝔸[K]`, and the quotient `𝔸[K] / K` is Hausdorff.  An explicit neighbourhood of zero
meeting `K` only in `0` is the set of adeles of norm less than `1` at every infinite place and
integral at every finite place.

The infinite component cannot be dropped: `K` is dense in the finite adele ring.  Together with the
compactness of `𝔸[K] / K`, discreteness says that `K` is a cocompact lattice in `𝔸[K]`, the
additive fact underlying the compactness of the norm-one idele class group.

## Main results

* `TauCeti.GlobalNumberFields.eq_zero_of_forall_norm_lt_one_of_mem_integralAdeles`:
  the only element of `K` whose adele has norm less than `1` at every infinite place and is
  integral at every finite place is `0`.
* `TauCeti.GlobalNumberFields.discreteTopology_principalSubgroup`: `K` is discrete in `𝔸[K]`.
* `TauCeti.GlobalNumberFields.isClosed_principalSubgroup`: `K` is closed in `𝔸[K]`.
* `TauCeti.GlobalNumberFields.t3Space_quotient_principalSubgroup`: `𝔸[K] / K` is Hausdorff.
* `TauCeti.GlobalNumberFields.principalSubalgebra`: the diagonal `K`-subalgebra of `𝔸[K]`, with its
  discrete topology and closed inclusion into `𝔸[K]`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain HeightOneSpectrum NumberField
open scoped NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable (K : Type*) [Field K] [NumberField K]

variable {K} in
/-- The only element of a number field whose adele has norm less than `1` at every infinite place
and is integral at every finite place is `0`. -/
theorem eq_zero_of_forall_norm_lt_one_of_mem_integralAdeles {x : K}
    (hinf : ∀ w : InfinitePlace K, ‖(algebraMap K 𝔸[K] x).1 w‖ < 1)
    (hfin : (algebraMap K 𝔸[K] x).2 ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K) :
    x = 0 := by
  obtain ⟨a, rfl⟩ := (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff (R := 𝓞 K) x).mp hfin
  have hlt (w : InfinitePlace K) : w (algebraMap (𝓞 K) K a) < 1 :=
    by
    simpa only [NumberField.AdeleRing.algebraMap_fst_apply,
      InfiniteAdeleRing.algebraMap_apply,
      NumberField.InfinitePlace.Completion.algebraMap_apply_eq_coe,
      AbsoluteValue.Completion.norm_coe, WithAbs.ofAbs_toAbs, WithAbs.equiv_apply,
      InfinitePlace.coe_apply] using hinf w
  by_contra ha
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact (hlt w).not_ge <| InfinitePlace.one_le_of_lt_one (by simpa using ha) fun z _ ↦ hlt z

/-- **`K` is discrete in its adele ring**: the diagonal copy of a number field is a discrete
additive subgroup of `𝔸[K]`. -/
instance discreteTopology_principalSubgroup :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by
  let U : Set 𝔸[K] := (⋂ w : InfinitePlace K, {a | ‖a.1 w‖ < 1}) ∩
    {a | a.2 ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K}
  have hU : IsOpen U := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun w ↦ isOpen_lt
        (continuous_norm.comp ((continuous_apply w).comp continuous_fst)) continuous_const
    · exact (FiniteAdeleRing.isOpen_integralAdeles (𝓞 K) K).preimage continuous_snd
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hU.preimage continuous_subtypeVal
  ext ⟨_, x, rfl⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_ofPred_eq, U]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl : x = 0 := (AdeleRing.algebraMap_injective (𝓞 K) K).eq_iff.mp <| by
      simpa using congrArg Subtype.val h
    exact ⟨fun w ↦ by
      -- The diagonal adele's coordinate is definitionally this field algebra map;
      -- expose that coordinate so simplification can use `map_zero` and `norm_zero`.
      change ‖(algebraMap K w.Completion) 0‖ < 1
      simp,
      (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff (R := 𝓞 K) 0).mpr ⟨0, map_zero _⟩⟩
  · obtain rfl := eq_zero_of_forall_norm_lt_one_of_mem_integralAdeles h.1 h.2
    simp

/-- **`K` is closed in its adele ring**: the diagonal copy of a number field is a closed additive
subgroup of `𝔸[K]`. -/
theorem isClosed_principalSubgroup :
    IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) :=
  AddSubgroup.isClosed_of_discreteTopology

/-- The quotient `𝔸[K] / K` of the adele ring of a number field by its diagonal copy of `K` is
Hausdorff, and indeed regular. -/
instance t3Space_quotient_principalSubgroup :
    T3Space (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) :=
  haveI := isClosed_principalSubgroup K
  inferInstance

/-- The diagonal copy of `K` in its adele ring `𝔸[K]`, packaged as a `K`-subalgebra (the range of
`Algebra.ofId K 𝔸[K]`). Its underlying set coincides with
`NumberField.AdeleRing.principalSubgroup (𝓞 K) K`. -/
noncomputable def principalSubalgebra : Subalgebra K 𝔸[K] :=
  (Algebra.ofId K 𝔸[K]).range

/-- The underlying set of `principalSubalgebra K` is that of
`AdeleRing.principalSubgroup (𝓞 K) K`. -/
@[simp]
theorem coe_principalSubalgebra :
    (principalSubalgebra K : Set 𝔸[K]) = (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) := by
  ext x
  simp [principalSubalgebra]

variable {K} in
@[simp]
theorem mem_principalSubalgebra_iff {x : 𝔸[K]} :
    x ∈ principalSubalgebra K ↔ ∃ c : K, algebraMap K 𝔸[K] c = x := by
  simp [principalSubalgebra, Algebra.mem_bot]

/-- Canonical `K`-algebra isomorphism between `K` and its diagonal copy `principalSubalgebra K` in
`𝔸[K]`. -/
noncomputable def principalSubalgebraEquiv : K ≃ₐ[K] principalSubalgebra K :=
  AlgEquiv.ofInjective (Algebra.ofId K 𝔸[K])
    (fun _ _ h ↦ AdeleRing.algebraMap_injective (𝓞 K) K h)

@[simp]
theorem coe_principalSubalgebraEquiv_apply (c : K) :
    (principalSubalgebraEquiv K c : 𝔸[K]) = algebraMap K 𝔸[K] c := by
  have h : (principalSubalgebra K).val.comp (principalSubalgebraEquiv K).toAlgHom =
      Algebra.ofId K 𝔸[K] := by ext
  exact AlgHom.congr_fun h c

/-- The diagonal `K`-subalgebra `principalSubalgebra K` is discrete in `𝔸[K]`. -/
instance discreteTopology_principalSubalgebra :
    DiscreteTopology (principalSubalgebra K) := by
  rw [← SetLike.isDiscrete_iff_discreteTopology, coe_principalSubalgebra,
    SetLike.isDiscrete_iff_discreteTopology]
  infer_instance

/-- The diagonal `K`-subalgebra `principalSubalgebra K` is closed in `𝔸[K]`. -/
theorem isClosed_principalSubalgebra :
    IsClosed (principalSubalgebra K : Set 𝔸[K]) := by
  rw [coe_principalSubalgebra]
  exact isClosed_principalSubgroup K

/-- The inclusion `(principalSubalgebra K).val : principalSubalgebra K →ₐ[K] 𝔸[K]` is a closed
topological embedding. -/
theorem isClosedEmbedding_principalSubalgebra_val :
    Topology.IsClosedEmbedding (principalSubalgebra K).val := by
  rw [Subalgebra.coe_val]
  exact Topology.IsClosedEmbedding.subtypeVal (isClosed_principalSubalgebra K)

end TauCeti.GlobalNumberFields

