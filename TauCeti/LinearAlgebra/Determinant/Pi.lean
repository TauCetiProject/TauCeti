/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import TauCeti.LinearAlgebra.Determinant.Line
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Rank
import TauCeti.LinearAlgebra.LinearIndependent.Fin

/-!
# Determinant lines of finite products of even-dimensional spaces

For two finite-dimensional spaces the determinant line of a product is the tensor product of the
determinant lines, `det U ⊗ det W ≃ det (U × W)` (`TauCeti.detLineProdEquiv`), and exchanging the
factors costs the sign `(-1) ^ (dim U * dim W)`
(`TauCeti.detLineCongr_prodComm_detLineProdEquiv`). For a finite family of spaces `U i` the
analogous isomorphism with an ordered tensor product depends on an ordering of the family, up to
the signs of the transpositions it involves. When every `U i` has even dimension all these signs
are `+1`, and the isomorphism needs no ordering at all: it is an isomorphism

`⨂ᵢ det (U i) ≃ det (Πᵢ U i)`

with the unordered tensor product `PiTensorProduct` (`TauCeti.detLinePiEquiv`). It sends
`⨂ᵢ ωᵢ` to the exterior product of the images of the `ωᵢ` under the inclusions
`U i → Πⱼ U j`. Elements of even exterior degree are central
(`TauCeti.ExteriorAlgebra.mem_center_of_mem_of_even`), so this product does not depend on the
order of its factors: for every enumeration `e` of the index set it is the product of the factors
in the order of `e` (`TauCeti.coe_detLinePiEquiv_tprod`). This is the permutation law of
determinant lines for even-dimensional factors.

This is how an orientation of each of finitely many even-dimensional spaces, for instance the
tangent spaces of the moduli spaces of the components of a configuration of pseudoholomorphic
curves, orients their product without any choice of an order of the components. The tangent space
of the moduli of a complex-oriented component has even real dimension, and the configuration
moduli are products over the unordered set of components.

## Main results

* `TauCeti.detLinePiEquiv`: for even-dimensional `U i`, the isomorphism
  `⨂ᵢ det (U i) ≃ det (Πᵢ U i)`.
* `TauCeti.coe_detLinePiEquiv_tprod`: its value on `⨂ᵢ ωᵢ`, as the product of the images of the
  `ωᵢ` taken in the order of any enumeration of the index set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant line bundles).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893.
-/

public section

noncomputable section

open Module
open scoped TensorProduct

namespace TauCeti

variable (K : Type*) [Field K] {ι : Type*} [DecidableEq ι] (U : ι → Type*)
  [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]

/-- The inclusion `det (U i) → ⋀ (Πⱼ U j)` induced by the inclusion of the `i`th factor, with
values in the center of the exterior algebra since `U i` has even dimension. -/
private def detLineSingle (h : ∀ i, Even (finrank K (U i))) (i : ι) :
    detLine K (U i) →ₗ[K] Subalgebra.center K (ExteriorAlgebra K ((i : ι) → U i)) where
  toFun x := ⟨ExteriorAlgebra.map (LinearMap.single K U i) (x : ExteriorAlgebra K (U i)),
    ExteriorAlgebra.mem_center_of_mem_of_even
      (ExteriorAlgebra.map_mem_exteriorPower _ x.2) (h i)⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

private theorem coe_detLineSingle_apply (h : ∀ i, Even (finrank K (U i))) (i : ι)
    (x : detLine K (U i)) :
    (detLineSingle K U h i x : ExteriorAlgebra K ((i : ι) → U i)) =
      ExteriorAlgebra.map (LinearMap.single K U i) (x : ExteriorAlgebra K (U i)) :=
  (rfl)

/-- The product over a finite set of the images of elements of the determinant lines lies in the
exterior power of the sum of their dimensions. -/
private theorem coe_prod_detLineSingle_mem (h : ∀ i, Even (finrank K (U i)))
    (x : (i : ι) → detLine K (U i)) (s : Finset ι) :
    ((∏ i ∈ s, detLineSingle K U h i (x i) : Subalgebra.center K _) :
        ExteriorAlgebra K ((i : ι) → U i)) ∈ ⋀[K]^(∑ i ∈ s, finrank K (U i)) ((i : ι) → U i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Subalgebra.coe_mul]
    exact SetLike.mul_mem_graded (ExteriorAlgebra.map_mem_exteriorPower _ (x a).2) ih

variable [∀ i, FiniteDimensional K (U i)]

/-- The family of exterior products of the bases `Module.finBasis K (U i)`, pushed into `Πᵢ U i`
and multiplied along a list of distinct indices, is the exterior product of a linearly independent
family of vectors vanishing at the indices off the list. -/
private theorem exists_linearIndependent_prod_map_eq_ιMulti (l : List ι) (hl : l.Nodup) :
    ∃ N, ∃ v : Fin N → ((i : ι) → U i), LinearIndependent K v ∧ (∀ k, ∀ j ∉ l, v k j = 0) ∧
      (l.map fun i ↦ ExteriorAlgebra.ιMulti K _
        (LinearMap.single K U i ∘ Module.finBasis K (U i))).prod =
        ExteriorAlgebra.ιMulti K N v := by
  induction l with
  | nil => exact ⟨0, Fin.elim0, linearIndependent_empty_type, fun k ↦ k.elim0, by simp⟩
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨N, v, hv, hsupp, heq⟩ := ih hl.2
    refine ⟨_, Fin.append (LinearMap.single K U a ∘ Module.finBasis K (U a)) v, ?_, ?_, ?_⟩
    · refine linearIndependent_fin_append.2 ⟨(Module.finBasis K (U a)).linearIndependent.map'
        _ (LinearMap.ker_eq_bot.2 fun x y hxy ↦ by simpa using congrFun hxy a), hv, ?_⟩
      -- The first block lies in the `a`th factor, the second vanishes at `a`.
      have h₁ : Submodule.span K (Set.range (LinearMap.single K U a ∘ Module.finBasis K (U a))) ≤
          LinearMap.range (LinearMap.single K U a) :=
        Submodule.span_le.2 (Set.range_subset_iff.2 fun k ↦ LinearMap.mem_range_self _ _)
      have h₂ : Submodule.span K (Set.range v) ≤ LinearMap.ker (LinearMap.proj a) :=
        Submodule.span_le.2 (Set.range_subset_iff.2 fun k ↦ hsupp k a hl.1)
      refine Submodule.disjoint_def.2 fun x hx hx' ↦ ?_
      obtain ⟨y, rfl⟩ := h₁ hx
      have hy : y = 0 := by simpa using h₂ hx'
      simp [hy]
    · intro k j hj
      rw [List.mem_cons, not_or] at hj
      induction k using Fin.addCases with
      | left k => simp [hj.1]
      | right k => simpa using hsupp k j hj.2
    · rw [List.map_cons, List.prod_cons, heq, ExteriorAlgebra.ιMulti_mul_ιMulti]

variable [Fintype ι]

/-- The multilinear map `(ωᵢ)ᵢ ↦ ∏ᵢ ωᵢ` from the determinant lines of the `U i` to that of
`Πᵢ U i`, the product being taken in the center of the exterior algebra. -/
private def detLinePiMultilinear (h : ∀ i, Even (finrank K (U i))) :
    ((i : ι) → detLine K (U i)) →ₘₗ[K] detLine K ((i : ι) → U i) :=
  ((Subalgebra.center K _).val.toLinearMap.compMultilinearMap
      ((MultilinearMap.mkPiAlgebra K ι (Subalgebra.center K _)).compLinearMap
        (detLineSingle K U h))).codRestrict _ fun x ↦ by
    simpa [MultilinearMap.mkPiAlgebra_apply, Module.finrank_pi_fintype] using
      coe_prod_detLineSingle_mem K U h x Finset.univ

/-- The value of `PiTensorProduct.lift (detLinePiMultilinear K U h)` on `⨂ᵢ ωᵢ`: the product of
the images of the `ωᵢ`, in the order of an enumeration `e` of the index set. -/
private theorem coe_lift_detLinePiMultilinear_tprod (h : ∀ i, Even (finrank K (U i)))
    (x : (i : ι) → detLine K (U i)) (e : Fin (Fintype.card ι) ≃ ι) :
    (PiTensorProduct.lift (detLinePiMultilinear K U h) (⨂ₜ[K] i, x i) :
        ExteriorAlgebra K ((i : ι) → U i)) =
      (List.ofFn fun k ↦ ExteriorAlgebra.map (LinearMap.single K U (e k))
        (x (e k) : ExteriorAlgebra K (U (e k)))).prod := by
  simp only [PiTensorProduct.lift.tprod, detLinePiMultilinear,
    MultilinearMap.codRestrict_apply_coe, LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, ← e.prod_comp,
    ← List.prod_ofFn, AlgHom.toLinearMap_apply, map_list_prod, List.map_ofFn,
    Function.comp_def, Subalgebra.coe_val, coe_detLineSingle_apply]

/-- `PiTensorProduct.lift (detLinePiMultilinear K U h)` is bijective: it is a map between lines
(`LinearMap.bijective_of_ne_zero`), nonzero on the tensor product of the exterior products of
bases. -/
private theorem bijective_lift_detLinePiMultilinear (h : ∀ i, Even (finrank K (U i))) :
    Function.Bijective (PiTensorProduct.lift (detLinePiMultilinear K U h)) := by
  set f := PiTensorProduct.lift (detLinePiMultilinear K U h)
  -- The source is a line: it has a basis indexed by the one-point type `Πᵢ Fin 1`.
  let b := Basis.piTensorProduct fun i ↦
    finBasisOfFinrankEq K (detLine K (U i)) (finrank_detLine K (U i))
  have : IsSimpleModule K (⨂[K] i, detLine K (U i)) :=
    isSimpleModule_iff_finrank_eq_one.2 (by simp [Module.finrank_eq_card_basis b])
  have : IsSimpleModule K (detLine K ((i : ι) → U i)) :=
    isSimpleModule_iff_finrank_eq_one.2 (finrank_detLine K _)
  -- `f` does not vanish on the tensor product of the exterior products of bases.
  refine LinearMap.bijective_of_ne_zero (M := ⨂[K] i, detLine K (U i))
    (N := detLine K ((i : ι) → U i)) fun hf ↦ ?_
  set e := (Fintype.equivFin ι).symm
  obtain ⟨N, v, hv, -, heq⟩ := exists_linearIndependent_prod_map_eq_ιMulti K U
    (List.ofFn e) (List.nodup_ofFn.2 e.injective)
  have h0 := coe_lift_detLinePiMultilinear_tprod K U h
    (fun i ↦ exteriorPower.ιMulti K _ (Module.finBasis K (U i))) e
  refine (exteriorPower.ιMulti_ne_zero_iff v).2 hv (Subtype.ext ?_)
  rw [exteriorPower.ιMulti_apply_coe, ← heq, ZeroMemClass.coe_zero, List.map_ofFn]
  calc _ = (f (⨂ₜ[K] i, exteriorPower.ιMulti K _ (Module.finBasis K (U i))) :
        ExteriorAlgebra K ((i : ι) → U i)) := by
        rw [h0]
        simp [Function.comp_def, ExteriorAlgebra.map_apply_ιMulti]
    _ = 0 := by rw [hf, LinearMap.zero_apply, ZeroMemClass.coe_zero]

/-- **The determinant line of a product of even-dimensional spaces.** If every `U i` has even
dimension, the determinant line of `Πᵢ U i` is the tensor product of the determinant lines of the
`U i`, over the unordered index set: `⨂ᵢ det (U i) ≃ det (Πᵢ U i)`. It sends `⨂ᵢ ωᵢ` to the
exterior product of the images of the `ωᵢ` under the inclusions of the factors, which may be
taken in any order (`TauCeti.coe_detLinePiEquiv_tprod`). -/
def detLinePiEquiv (h : ∀ i, Even (finrank K (U i))) :
    (⨂[K] i, detLine K (U i)) ≃ₗ[K] detLine K ((i : ι) → U i) :=
  LinearEquiv.ofBijective _ (bijective_lift_detLinePiMultilinear K U h)

/-- **The permutation law.** `TauCeti.detLinePiEquiv` sends `⨂ᵢ ωᵢ` to the exterior product of the
images of the `ωᵢ` under the inclusions of the factors, taken in the order of any enumeration
`e` of the index set. In particular this product does not depend on `e`. -/
theorem coe_detLinePiEquiv_tprod (h : ∀ i, Even (finrank K (U i)))
    (x : (i : ι) → detLine K (U i)) (e : Fin (Fintype.card ι) ≃ ι) :
    (detLinePiEquiv K U h (⨂ₜ[K] i, x i) : ExteriorAlgebra K ((i : ι) → U i)) =
      (List.ofFn fun k ↦ ExteriorAlgebra.map (LinearMap.single K U (e k))
        (x (e k) : ExteriorAlgebra K (U (e k)))).prod :=
  coe_lift_detLinePiMultilinear_tprod K U h x e

end TauCeti
