/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PontryaginDual
public import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Algebra.BigOperators.Finprod
import TauCeti.Topology.Algebra.RestrictedProduct.ProductLevel

/-!
# Pontryagin dual of a restricted product

`PontryaginDual.restrictedProductMulEquiv` identifies continuous characters of a restricted
product with families of local characters trivial on almost every reference subgroup.
Mathlib's `PontryaginDual.map` gives restriction. Reconstruction is by `finprod`, with finite
support given by `RestrictedProduct.finite_mulSupport_apply`. The criterion
`Subgroup.mem_of_forall_mulSingle_mem` gives uniqueness from agreement on the individual factors.

See J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Lemmas 3.2.1–3.2.2.
-/

public section

open Filter Topology
open scoped RestrictedProduct

namespace PontryaginDual

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  (B : ∀ i, Subgroup (G i))

/-- Restriction of a character along the inclusion of one factor of a restricted product. -/
noncomputable def restrictMulSingle (i : ι) :
    PontryaginDual (Πʳ j, [G j, B j]) →ₜ* PontryaginDual (G i) :=
  let : DecidableEq ι := Classical.typeDecidableEq ι
  PontryaginDual.map
    ⟨RestrictedProduct.mulSingleMonoidHom B i, TauCeti.continuous_restrictedProduct_mulSingle B i⟩

/-- Evaluate a restricted character by inserting its argument in the chosen factor. -/
@[simp]
theorem restrictMulSingle_apply_apply [inst : DecidableEq ι]
    (χ : PontryaginDual (Πʳ i, [G i, B i])) (i : ι) (x : G i) :
    restrictMulSingle B i χ x = χ (RestrictedProduct.mulSingle B i x) := by
  cases (Subsingleton.elim (Classical.typeDecidableEq ι) inst)
  exact (rfl)

/-- A character of a restricted product is trivial on cofinitely many reference subgroups. -/
theorem eventually_restrictMulSingle_mem_pontryaginAnnihilator
    (χ : PontryaginDual (Πʳ i, [G i, B i])) :
    ∀ᶠ i in cofinite, restrictMulSingle B i χ ∈ (B i).pontryaginAnnihilator := by
  classical
  let f := RestrictedProduct.structureMap G (fun i ↦ (B i : Set (G i))) cofinite
  let U := Circle.centeredArc (Real.pi / 2)
  have h1 : χ (f 1) = 1 := _root_.map_one χ
  have hf : Continuous (χ ∘ f) :=
    (map_continuous χ).comp RestrictedProduct.isEmbedding_structureMap.continuous
  have hU : (χ ∘ f) ⁻¹' U ∈ 𝓝 (1 : ∀ i, B i) :=
    ((Circle.isOpen_centeredArc _).preimage hf).mem_nhds <| by
      rw [Set.mem_preimage, Function.comp_apply, h1]
      exact ⟨0, by simp [Real.pi_pos], Circle.exp_zero⟩
  -- The arc condition on a product neighbourhood constrains only finitely many coordinates.
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, V, hV, hSV⟩ := hU
  filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
  refine Subgroup.mem_pontryaginAnnihilator.mpr fun x hx ↦
    Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ ↦ ?_
  have hmem : Pi.mulSingle i (⟨x ^ n, (B i).pow_mem hx n⟩ : B i) ∈ (χ ∘ f) ⁻¹' U :=
    hSV fun j hj ↦ by
      rw [Pi.mulSingle_eq_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact mem_of_mem_nhds (hV j)
  have heq : f (Pi.mulSingle i (⟨x ^ n, (B i).pow_mem hx n⟩ : B i)) =
      RestrictedProduct.mulSingle B i (x ^ n) := by
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp [f, RestrictedProduct.structureMap_apply]
    · simp [f, RestrictedProduct.structureMap_apply, Pi.mulSingle_eq_of_ne hj,
        RestrictedProduct.mulSingle_eq_of_ne _ _ hj]
  simpa only [Set.mem_preimage, Function.comp_apply, heq, restrictMulSingle_apply_apply,
    RestrictedProduct.mulSingle_pow, map_pow] using hmem

/-- In the evaluation of a restricted family of characters on a restricted product element,
only finitely many local values differ from one. -/
theorem _root_.RestrictedProduct.finite_mulSupport_apply {B : ∀ i, Subgroup (G i)}
    (ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator])
    (x : Πʳ i, [G i, B i]) : (Function.mulSupport fun i ↦ ψ i (x i)).Finite := by
  have h : ∀ᶠ i in cofinite, ψ i (x i) = 1 := by
    filter_upwards [ψ.eventually, x.eventually] with i hψ hx
    exact Subgroup.mem_pontryaginAnnihilator.mp hψ _ hx
  exact Filter.mem_cofinite.mp h

/-- The finite product of the local character values is continuous on the restricted product. -/
theorem _root_.RestrictedProduct.continuous_finprod_character_apply {B : ∀ i, Subgroup (G i)}
    (ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) :
    Continuous fun x : (Πʳ i, [G i, B i]) ↦ ∏ᶠ i, ψ i (x i) := by
  -- On a principal stage a single finite set suffices for every evaluation.
  refine RestrictedProduct.continuous_dom.mpr fun S hS ↦ ?_
  classical
  have hcof : S ∈ (cofinite : Filter ι) := le_principal_iff.mp hS
  have hT : {i | i ∈ S ∧ ψ i ∈ (B i).pontryaginAnnihilator}ᶜ.Finite :=
    Filter.mem_cofinite.mp (Filter.Eventually.and hcof ψ.eventually)
  refine (continuous_finsetProd hT.toFinset fun i _ ↦ (map_continuous (ψ i)).comp
    (RestrictedProduct.continuous_eval i)).congr fun x ↦ ?_
  simp only [Function.comp_apply, RestrictedProduct.inclusion_apply]
  symm
  refine finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ hT.mem_toFinset.mpr ?_
  intro hiT
  exact hi (Subgroup.mem_pontryaginAnnihilator.mp hiT.2 _
    (eventually_principal.mp x.eventually i hiT.1))

/-- Restriction to the factors identifies characters of a restricted product with families of
characters trivial on the reference subgroups at all but finitely many indices. -/
noncomputable def restrictedProductMulEquiv :
    PontryaginDual (Πʳ i, [G i, B i]) ≃*
      (Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) :=
  let : DecidableEq ι := Classical.typeDecidableEq ι
  let restrict (χ : PontryaginDual (Πʳ i, [G i, B i])) :
      Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator] :=
    ⟨fun i ↦ restrictMulSingle B i χ, eventually_restrictMulSingle_mem_pontryaginAnnihilator B χ⟩
  let assemble (ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) :
      PontryaginDual (Πʳ i, [G i, B i]) :=
    { toFun := fun x ↦ ∏ᶠ i, ψ i (x i)
      map_one' := finprod_eq_one_of_forall_eq_one fun i ↦ by simp
      map_mul' := fun x y ↦ by
        simp only [RestrictedProduct.mul_apply, _root_.map_mul]
        exact finprod_mul_distrib (ψ.finite_mulSupport_apply x) (ψ.finite_mulSupport_apply y)
      continuous_toFun := ψ.continuous_finprod_character_apply }
  have hsingle (ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) (i : ι)
      (x : G i) : assemble ψ (RestrictedProduct.mulSingle B i x) = ψ i x := by
    have heq : assemble ψ (RestrictedProduct.mulSingle B i x) =
        ∏ᶠ j, ψ j (RestrictedProduct.mulSingle B i x j) := rfl
    rw [heq, finprod_eq_single _ i]
    · simp
    · intro j hj
      simp [RestrictedProduct.mulSingle_eq_of_ne _ _ hj]
  { toFun := restrict
    invFun := assemble
    left_inv := fun χ ↦ by
      apply PontryaginDual.ext
      intro x
      let U := MonoidHom.eqLocus (assemble (restrict χ) : _ →ₜ* Circle).toMonoidHom
        (χ : _ →ₜ* Circle).toMonoidHom
      have hclosed : IsClosed (U : Set (Πʳ i, [G i, B i])) :=
        isClosed_eq (map_continuous (assemble (restrict χ))) (map_continuous χ)
      exact U.mem_of_forall_mulSingle_mem hclosed fun i ↦ hsingle (restrict χ) i (x i)
    right_inv := fun ψ ↦ RestrictedProduct.ext _ _ (fun i ↦ PontryaginDual.ext (hsingle ψ i))
    map_mul' := fun χ ψ ↦ RestrictedProduct.ext _ _ (fun i ↦ PontryaginDual.ext fun _ ↦ rfl) }

/-- Evaluation rule for the forward equivalence. Each coordinate is restriction to its factor. -/
@[simp]
theorem restrictedProductMulEquiv_apply
    (χ : PontryaginDual (Πʳ i, [G i, B i])) (i : ι) :
    restrictedProductMulEquiv B χ i = restrictMulSingle B i χ := (rfl)

/-- Evaluation rule for the inverse equivalence. The reconstructed character is the finite
product of the local values. -/
@[simp]
theorem restrictedProductMulEquiv_symm_apply_apply
    (ψ : Πʳ i, [PontryaginDual (G i), (B i).pontryaginAnnihilator]) (x : Πʳ i, [G i, B i]) :
    (restrictedProductMulEquiv B).symm ψ x = ∏ᶠ i, ψ i (x i) := (rfl)

end PontryaginDual
