/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Prod
public import TauCeti.Geometry.Toric.Delzant.Prod
public import TauCeti.Geometry.Toric.Delzant.Quotient.Symplectic

import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The Delzant quotient of a product of polytopes

Let `i : N →+ V` and `i' : N' →+ V'` be lattices with facet presentations `(u, c)` and `(u', c')`
of polytopes `Δ` and `Δ'`. Their product `Δ × Δ'` has the facet presentation
`(prodNormal u u', Sum.elim c c')` in the product lattice `i × i' : N × N' →+ V × V'`
(`TauCeti.Geometry.Toric.Delzant.Prod`). This file shows that Delzant's construction turns this
product into the product of the Delzant quotients: the Delzant quotient of `Δ × Δ'` is
`M_Δ × M_Δ'`, as smooth manifolds with the product torus action and the product moment map. For
instance, presenting the rectangle `[0, a] × [0, b]` as the product of two intervals exhibits its
Delzant quotient, the toric `S² × S²`, as the product of the Delzant quotients of the two
intervals.

* **The level and the kernel torus.** Splitting the coordinates of `ℂ^(ι ⊕ ι')` along `ι ⊕ ι'`
  (`TauCeti.Toric.sumCoordEquiv`) identifies the moment map of `(ℝ / 2πℤ)^(ι ⊕ ι')` with the sum
  of the moment maps of the factors, and the kernel `𝔫` of `β_ℝ` with the product of the kernels
  (`TauCeti.Toric.mem_ker_linearCombination_prodNormal_iff`).
  So the level of the product presentation is the product of the levels
  (`TauCeti.Toric.mem_delzantLevel_prod_iff`, `TauCeti.Toric.delzantLevelProdHomeomorph`), and the
  kernel torus of the product is the product of the kernel tori
  (`TauCeti.Toric.mem_ker_facetTorusHom_prod_iff`); the splitting intertwines the torus actions.
* **The quotient.** Hence the identification of the levels descends to a homeomorphism
  `M_(Δ × Δ') ≃ M_Δ × M_Δ'` (`TauCeti.Toric.DelzantQuotient.prodHomeomorph`). It intertwines the
  residual torus of the product with the product of the residual tori
  (`TauCeti.Toric.DelzantQuotient.prodHomeomorph_coe_vadd`), and carries the reduced moment map of
  the product to the pair of the reduced moment maps of the factors, under
  `V* × V'* ≃ (V × V')*` (`TauCeti.Toric.DelzantQuotient.reducedMomentMap_eq_coprod`).
* **Smoothness.** For Delzant presentations in integral lattices, the product presentation is
  Delzant (`TauCeti.Toric.IsDelzant.prod`), and both identifications are diffeomorphisms for the
  atlases of the levels and of the quotient manifolds
  (`TauCeti.Toric.IsDelzant.delzantLevelProdDiffeomorph`,
  `TauCeti.Toric.IsDelzant.delzantQuotientProdDiffeomorph`). For the quotients, smoothness of a
  map and of its inverse is read off the projections from the levels, which are surjective
  submersions.
* **The symplectic forms.** The standard symplectic form of `ℂ^(ι ⊕ ι')` is the sum of the
  standard forms of `ℂ^ι` and `ℂ^ι'` under the splitting
  (`TauCeti.Toric.stdSymplecticForm_sumCoordEquiv`). So the diffeomorphism of the levels pulls the
  product of the restricted forms back to the restricted form
  (`TauCeti.Toric.IsDelzant.mpullback_delzantLevelProdDiffeomorph_prod`), and the diffeomorphism
  of the quotients pulls the product form `ω_Δ ⊕ ω_Δ'` back to the reduced form `ω_(Δ × Δ')`
  (`TauCeti.Toric.IsDelzant.mpullback_delzantQuotientProdDiffeomorph_prod`): the Delzant quotient
  of a product is the symplectic product of the Delzant quotients.

## Main definitions

* `TauCeti.Toric.delzantLevelProdHomeomorph`: the level of the product is the product of the
  levels.
* `TauCeti.Toric.DelzantQuotient.prodHomeomorph`: the Delzant quotient of the product is the
  product of the Delzant quotients.
* `TauCeti.Toric.IsDelzant.delzantLevelProdDiffeomorph`,
  `TauCeti.Toric.IsDelzant.delzantQuotientProdDiffeomorph`: their smooth versions.

## Main results

* `TauCeti.Toric.mem_ker_facetTorusHom_prod_iff`: the kernel torus of the product.
* `TauCeti.Toric.DelzantQuotient.prodHomeomorph_coe_vadd`: equivariance for the residual tori.
* `TauCeti.Toric.DelzantQuotient.reducedMomentMap_eq_coprod`,
  `TauCeti.Toric.DelzantQuotient.reducedMomentMap_prodHomeomorph_symm`: the reduced moment map of
  the product is the product of the reduced moment maps.
* `TauCeti.Toric.IsDelzant.mpullback_delzantQuotientProdDiffeomorph_prod`: the identification
  `M_(Δ × Δ') ≃ M_Δ × M_Δ'` is a symplectomorphism for the reduced forms and the product form.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28–29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Real Module Manifold
open scoped ContDiff

namespace TauCeti.Toric

variable {ι ι' N N' V V' : Type*} [Fintype ι] [Fintype ι'] [AddCommGroup N] [AddCommGroup N']

/-! ### The kernel torus of a product -/

section Lattice

variable [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V'] {i : N →+ V}
  {i' : N' →+ V'} {u : ι → N} {u' : ι' → N'}

/-- **The kernel torus of a product.** An angle `θ ∈ (ℝ / pℤ)^(ι ⊕ ι')` lies in the kernel of the
torus homomorphism of the product normals exactly when its restrictions `θ ∘ inl` and `θ ∘ inr` lie
in the kernels for the two factors. -/
theorem mem_ker_facetTorusHom_prod_iff {p : ℝ} {θ : ι ⊕ ι' → AddCircle p} :
    θ ∈ (facetTorusHom (i.prodMap i') (prodNormal u u') p).ker ↔
      θ ∘ .inl ∈ (facetTorusHom i u p).ker ∧ θ ∘ .inr ∈ (facetTorusHom i' u' p).ker := by
  obtain ⟨t, rfl⟩ := (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples p)).comp_left θ
  simp only [AddMonoidHom.mem_ker, Function.comp_def]
  rw [facetTorusHom_coe, facetTorusHom_coe, facetTorusHom_coe,
    linearCombination_prodNormal_apply]
  simp [Prod.ext_iff, Function.comp_def]

end Lattice

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {u : ι → N} {u' : ι' → N'} {c : ι → ℝ} {c' : ι' → ℝ}

/-! ### Splitting the coordinates of `ℂ^(ι ⊕ ι')` -/

variable (ι ι') in
/-- The splitting `ℂ^(ι ⊕ ι') ≃ ℂ^ι × ℂ^ι'` of the coordinates of `ℂ^(ι ⊕ ι')`, in the real
coordinates `z_j = q_j + i p_j` used for the Delzant level: the point `(q, p)` goes to the pair of
its restrictions `((q ∘ inl, p ∘ inl), (q ∘ inr, p ∘ inr))`. -/
def sumCoordEquiv :
    (EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι')) ≃L[ℝ]
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) × (EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι') :=
  let s : EuclideanSpace ℝ (ι ⊕ ι') ≃L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι' :=
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 fun _ : ι ⊕ ι' ↦ ℝ).toContinuousLinearEquiv.trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ _ _)
  (s.prodCongr s).trans (ContinuousLinearEquiv.prodProdProdComm ℝ _ _ _ _)

@[simp]
theorem sumCoordEquiv_apply_fst_fst (x : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι'))
    (j : ι) : (sumCoordEquiv ι ι' x).1.1 j = x.1 (.inl j) :=
  (rfl)

@[simp]
theorem sumCoordEquiv_apply_fst_snd (x : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι'))
    (j : ι) : (sumCoordEquiv ι ι' x).1.2 j = x.2 (.inl j) :=
  (rfl)

@[simp]
theorem sumCoordEquiv_apply_snd_fst (x : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι'))
    (j : ι') : (sumCoordEquiv ι ι' x).2.1 j = x.1 (.inr j) :=
  (rfl)

@[simp]
theorem sumCoordEquiv_apply_snd_snd (x : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι'))
    (j : ι') : (sumCoordEquiv ι ι' x).2.2 j = x.2 (.inr j) :=
  (rfl)

@[simp]
theorem sumCoordEquiv_symm_apply_fst (y : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
    (EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι')) (j : ι ⊕ ι') :
    ((sumCoordEquiv ι ι').symm y).1 j = Sum.elim y.1.1 y.2.1 j := by
  cases j <;> rfl

@[simp]
theorem sumCoordEquiv_symm_apply_snd (y : (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) ×
    (EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι')) (j : ι ⊕ ι') :
    ((sumCoordEquiv ι ι').symm y).2 j = Sum.elim y.1.2 y.2.2 j := by
  cases j <;> rfl

/-- Splitting the coordinates intertwines the rotation by `θ ∈ (ℝ / 2πℤ)^(ι ⊕ ι')` with the
rotations by its restrictions `θ ∘ inl` and `θ ∘ inr`. -/
theorem sumCoordEquiv_torusRotation (θ : ι ⊕ ι' → AddCircle (2 * π))
    (x : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι')) :
    sumCoordEquiv ι ι' (torusRotation θ x) =
      (torusRotation (θ ∘ .inl) (sumCoordEquiv ι ι' x).1,
        torusRotation (θ ∘ .inr) (sumCoordEquiv ι ι' x).2) := by
  ext j <;> simp [torusRotation_apply_fst, torusRotation_apply_snd]

/-- **The standard symplectic form splits along `ι ⊕ ι'`.** The standard symplectic form of
`ℂ^(ι ⊕ ι')` is the sum of the standard symplectic forms of `ℂ^ι` and `ℂ^ι'` on the two parts of
the splitting of the coordinates. -/
theorem stdSymplecticForm_sumCoordEquiv
    (x y : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι')) :
    stdSymplecticForm x y =
      stdSymplecticForm (sumCoordEquiv ι ι' x).1 (sumCoordEquiv ι ι' y).1 +
        stdSymplecticForm (sumCoordEquiv ι ι' x).2 (sumCoordEquiv ι ι' y).2 := by
  simp only [stdSymplecticForm_apply, PiLp.inner_apply, Fintype.sum_sum_type,
    sumCoordEquiv_apply_fst_fst, sumCoordEquiv_apply_fst_snd, sumCoordEquiv_apply_snd_fst,
    sumCoordEquiv_apply_snd_snd]
  ring

/-- The standard symplectic form of `ℂ^(ι ⊕ ι')`, as a constant two-form, is the sum of the
pullbacks of the standard forms of `ℂ^ι` and `ℂ^ι'` along the two parts of the splitting of the
coordinates. -/
private theorem mpullback_fst_sumCoordEquiv_add_mpullback_snd_sumCoordEquiv :
    SmoothForm.mpullback
        ((ContinuousLinearMap.fst ℝ _ _).comp (sumCoordEquiv ι ι').toContinuousLinearMap)
        ((ContinuousLinearMap.fst ℝ _ _).comp
          (sumCoordEquiv ι ι').toContinuousLinearMap).contDiff.contMDiff
        (stdSymplecticForm (V := EuclideanSpace ℝ ι)).constSmooth +
      SmoothForm.mpullback
          ((ContinuousLinearMap.snd ℝ _ _).comp (sumCoordEquiv ι ι').toContinuousLinearMap)
          ((ContinuousLinearMap.snd ℝ _ _).comp
            (sumCoordEquiv ι ι').toContinuousLinearMap).contDiff.contMDiff
          (stdSymplecticForm (V := EuclideanSpace ℝ ι')).constSmooth =
      (stdSymplecticForm (V := EuclideanSpace ℝ (ι ⊕ ι'))).constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  rw [SmoothBundleForm.eval₂_add, SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback,
    SymplecticForm.eval₂_constSmooth_mfderiv_eq, SymplecticForm.eval₂_constSmooth_mfderiv_eq,
    SymplecticForm.fromTangentSpace_constSmooth_apply, mvfderiv_eq_fderiv, mvfderiv_eq_fderiv,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact (stdSymplecticForm_sumCoordEquiv _ _).symm

/-! ### The level of a product -/

/-- The moment map of `(ℝ / 2πℤ)^(ι ⊕ ι')` on `ℂ^(ι ⊕ ι')`, for the support constants
`Sum.elim c c'`, is the sum of the moment maps of the two factors. -/
theorem delzantMomentMap_sumElim_apply (x : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι'))
    (t : ι ⊕ ι' → ℝ) :
    delzantMomentMap (Sum.elim c c') x t =
      delzantMomentMap c (sumCoordEquiv ι ι' x).1 (t ∘ .inl) +
        delzantMomentMap c' (sumCoordEquiv ι ι' x).2 (t ∘ .inr) := by
  simp [Fintype.sum_sum_type]

/-- A point of `ℂ^(ι ⊕ ι')` lies on the level of the product presentation exactly when its two
parts lie on the levels of the factors. -/
@[simp]
theorem mem_delzantLevel_prod_iff {x : EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι')} :
    x ∈ delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c') ↔
      (sumCoordEquiv ι ι' x).1 ∈ delzantLevel i u c ∧
        (sumCoordEquiv ι ι' x).2 ∈ delzantLevel i' u' c' := by
  simp only [mem_delzantLevel, mem_ker_linearCombination_prodNormal_iff,
    delzantMomentMap_sumElim_apply]
  refine ⟨fun h ↦ ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩, fun h t ht ↦ by rw [h.1 _ ht.1, h.2 _ ht.2,
    add_zero]⟩
  · simpa using h (Sum.elim t 0) ⟨ht, by simp⟩
  · simpa using h (Sum.elim 0 t) ⟨by simp, ht⟩

variable (i i' u u' c c') in
/-- **The level of a product.** Splitting the coordinates identifies the level of the product
presentation with the product of the levels of the two factors. -/
def delzantLevelProdHomeomorph :
    delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c') ≃ₜ
      delzantLevel i u c × delzantLevel i' u' c' :=
  ((sumCoordEquiv ι ι').toHomeomorph.subtype fun _ ↦ mem_delzantLevel_prod_iff).trans
    (Homeomorph.Set.prod _ _)

@[simp]
theorem coe_delzantLevelProdHomeomorph_fst
    (x : delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c')) :
    ((delzantLevelProdHomeomorph i i' u u' c c' x).1 : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =
      (sumCoordEquiv ι ι' x).1 :=
  (rfl)

@[simp]
theorem coe_delzantLevelProdHomeomorph_snd
    (x : delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c')) :
    ((delzantLevelProdHomeomorph i i' u u' c c' x).2 :
        EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι') =
      (sumCoordEquiv ι ι' x).2 :=
  (rfl)

@[simp]
theorem coe_delzantLevelProdHomeomorph_symm (y : delzantLevel i u c × delzantLevel i' u' c') :
    ((delzantLevelProdHomeomorph i i' u u' c c').symm y :
        EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι')) =
      (sumCoordEquiv ι ι').symm (y.1, y.2) :=
  (rfl)

/-- The identification of the levels intertwines the action of `θ ∈ (ℝ / 2πℤ)^(ι ⊕ ι')` with the
actions of its restrictions `θ ∘ inl` and `θ ∘ inr` on the two factors. -/
@[simp]
theorem delzantLevelProdHomeomorph_vadd (θ : ι ⊕ ι' → AddCircle (2 * π))
    (x : delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c')) :
    delzantLevelProdHomeomorph i i' u u' c c' (θ +ᵥ x) =
      (θ ∘ .inl +ᵥ (delzantLevelProdHomeomorph i i' u u' c c' x).1,
        θ ∘ .inr +ᵥ (delzantLevelProdHomeomorph i i' u u' c c' x).2) := by
  ext : 1 <;> refine Subtype.ext ?_ <;>
    simp [sumCoordEquiv_torusRotation]

/-- The inverse identification of the levels sends the actions of `θ` and `θ'` on the factors to
the action of `Sum.elim θ θ'`. -/
@[simp]
theorem delzantLevelProdHomeomorph_symm_vadd (θ : ι → AddCircle (2 * π))
    (θ' : ι' → AddCircle (2 * π)) (y : delzantLevel i u c) (y' : delzantLevel i' u' c') :
    (delzantLevelProdHomeomorph i i' u u' c c').symm (θ +ᵥ y, θ' +ᵥ y') =
      Sum.elim θ θ' +ᵥ (delzantLevelProdHomeomorph i i' u u' c c').symm (y, y') := by
  rw [(delzantLevelProdHomeomorph i i' u u' c c').symm_apply_eq, delzantLevelProdHomeomorph_vadd,
    Homeomorph.apply_symm_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]

/-! ### The Delzant quotient of a product -/

namespace DelzantQuotient

/-- Acting on the two factors by elements of their kernel tori does not change the class of the
corresponding point of the level of the product. -/
private theorem mk_delzantLevelProdHomeomorph_symm_vadd {θ : ι → AddCircle (2 * π)}
    {θ' : ι' → AddCircle (2 * π)} (hθ : θ ∈ (facetTorusHom i u (2 * π)).ker)
    (hθ' : θ' ∈ (facetTorusHom i' u' (2 * π)).ker) (y : delzantLevel i u c)
    (y' : delzantLevel i' u' c') :
    mk ((delzantLevelProdHomeomorph i i' u u' c c').symm (θ +ᵥ y, θ' +ᵥ y')) =
      mk ((delzantLevelProdHomeomorph i i' u u' c c').symm (y, y')) := by
  have hm : Sum.elim θ θ' ∈ (facetTorusHom (i.prodMap i') (prodNormal u u') (2 * π)).ker :=
    mem_ker_facetTorusHom_prod_iff.2 ⟨by simpa using hθ, by simpa using hθ'⟩
  rw [delzantLevelProdHomeomorph_symm_vadd]
  exact mk_vadd_of_mem_ker hm _

variable (i i' u u' c c') in
/-- **The Delzant quotient of a product is the product of the Delzant quotients.** The
identification of the level of the product presentation with the product of the levels descends
to a homeomorphism `M_(Δ × Δ') ≃ M_Δ × M_Δ'`, sending the class of a point to the pair of classes
of its two parts. -/
def prodHomeomorph : DelzantQuotient (i.prodMap i') (prodNormal u u') (Sum.elim c c') ≃ₜ
    DelzantQuotient i u c × DelzantQuotient i' u' c' where
  toFun := lift (fun x ↦ (mk (delzantLevelProdHomeomorph i i' u u' c c' x).1,
      mk (delzantLevelProdHomeomorph i i' u u' c c' x).2)) fun θ hθ x ↦ by
    rw [delzantLevelProdHomeomorph_vadd, mk_vadd_of_mem_ker (mem_ker_facetTorusHom_prod_iff.1 hθ).1,
      mk_vadd_of_mem_ker (mem_ker_facetTorusHom_prod_iff.1 hθ).2]
  invFun q := lift (fun x ↦ lift (fun x' ↦ mk ((delzantLevelProdHomeomorph i i' u u' c c').symm
      (x, x'))) fun θ' hθ' x' ↦ by
        simpa using mk_delzantLevelProdHomeomorph_symm_vadd (zero_mem _) hθ' x x')
      (fun θ hθ x ↦ funext fun q' ↦ by
        induction q' using DelzantQuotient.inductionOn with | h x' =>
        simpa using mk_delzantLevelProdHomeomorph_symm_vadd hθ (zero_mem _) x x')
      q.1 q.2
  left_inv q := by
    induction q using DelzantQuotient.inductionOn with | h x => simp
  right_inv q := by
    obtain ⟨q, q'⟩ := q
    induction q using DelzantQuotient.inductionOn with | h x =>
    induction q' using DelzantQuotient.inductionOn with | h x' =>
    simp
  continuous_toFun := by
    have h := (delzantLevelProdHomeomorph i i' u u' c c').continuous
    exact continuous_lift _ <| (continuous_mk.comp (continuous_fst.comp h)).prodMk
      (continuous_mk.comp (continuous_snd.comp h))
  continuous_invFun := by
    refine (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff.1 ?_
    convert continuous_mk.comp (delzantLevelProdHomeomorph i i' u u' c c').symm.continuous
    ext ⟨x, x'⟩
    simp

@[simp]
theorem prodHomeomorph_mk (x : delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c')) :
    prodHomeomorph i i' u u' c c' (mk x) =
      (mk (delzantLevelProdHomeomorph i i' u u' c c' x).1,
        mk (delzantLevelProdHomeomorph i i' u u' c c' x).2) :=
  lift_mk _ _ x

@[simp]
theorem prodHomeomorph_symm_mk (y : delzantLevel i u c) (y' : delzantLevel i' u' c') :
    (prodHomeomorph i i' u u' c c').symm (mk y, mk y') =
      mk ((delzantLevelProdHomeomorph i i' u u' c c').symm (y, y')) := by
  rw [Homeomorph.symm_apply_eq, prodHomeomorph_mk, Homeomorph.apply_symm_apply]

/-- **The product homeomorphism is equivariant.** It intertwines the action of the class of
`θ ∈ (ℝ / 2πℤ)^(ι ⊕ ι')` in the residual torus of the product with the actions of the classes of
its restrictions `θ ∘ inl` and `θ ∘ inr` in the residual tori of the factors. -/
@[simp]
theorem prodHomeomorph_coe_vadd (θ : ι ⊕ ι' → AddCircle (2 * π))
    (q : DelzantQuotient (i.prodMap i') (prodNormal u u') (Sum.elim c c')) :
    prodHomeomorph i i' u u' c c'
        ((θ : (ι ⊕ ι' → AddCircle (2 * π)) ⧸
          (facetTorusHom (i.prodMap i') (prodNormal u u') (2 * π)).ker) +ᵥ q) =
      (((θ ∘ .inl : ι → AddCircle (2 * π)) :
          (ι → AddCircle (2 * π)) ⧸ (facetTorusHom i u (2 * π)).ker) +ᵥ
          (prodHomeomorph i i' u u' c c' q).1,
        ((θ ∘ .inr : ι' → AddCircle (2 * π)) :
          (ι' → AddCircle (2 * π)) ⧸ (facetTorusHom i' u' (2 * π)).ker) +ᵥ
          (prodHomeomorph i i' u u' c c' q).2) := by
  induction q using DelzantQuotient.inductionOn with | h x =>
  simp [coe_vadd_mk]

section ReducedMomentMap

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
  (hβ : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)))
  (hβ' : Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i' (u' j)))

/-- **The reduced moment map of a product.** Under the product homeomorphism, the reduced moment
map of `M_(Δ × Δ')` is the pair of the reduced moment maps of `M_Δ` and `M_Δ'`, under the
identification `V* × V'* ≃ (V × V')*`. -/
@[simp]
theorem reducedMomentMap_prodHomeomorph_symm
    (q : DelzantQuotient i u c × DelzantQuotient i' u' c') :
    reducedMomentMap (i := i.prodMap i') (u := prodNormal u u') (c := Sum.elim c c')
        (surjective_linearCombination_prodNormal hβ hβ') ((prodHomeomorph i i' u u' c c').symm q) =
      (reducedMomentMap hβ q.1).coprod (reducedMomentMap hβ' q.2) := by
  obtain ⟨q, q'⟩ := q
  induction q using DelzantQuotient.inductionOn with | h x =>
  induction q' using DelzantQuotient.inductionOn with | h x' =>
  rw [prodHomeomorph_symm_mk, reducedMomentMap_mk_eq_iff]
  rintro (j | j) <;> simp [reducedMomentMap_mk_apply]

/-- The reduced moment map of `M_(Δ × Δ')` at `q` is the pair of the reduced moment maps of `M_Δ`
and `M_Δ'` at the two components of the image of `q` under the product homeomorphism. -/
theorem reducedMomentMap_eq_coprod
    (q : DelzantQuotient (i.prodMap i') (prodNormal u u') (Sum.elim c c')) :
    reducedMomentMap (i := i.prodMap i') (u := prodNormal u u') (c := Sum.elim c c')
        (surjective_linearCombination_prodNormal hβ hβ') q =
      (reducedMomentMap hβ (prodHomeomorph i i' u u' c c' q).1).coprod
        (reducedMomentMap hβ' (prodHomeomorph i i' u u' c c' q).2) := by
  rw [← reducedMomentMap_prodHomeomorph_symm, Homeomorph.symm_apply_apply]

end ReducedMomentMap

end DelzantQuotient

/-! ### The smooth structures -/

namespace IsDelzant

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] (hΔ : IsDelzant i u c)
  (hΔ' : IsDelzant i' u' c') (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')

/-- **The level of a product is diffeomorphic to the product of the levels.** For Delzant
presentations in integral lattices, the identification `delzantLevelProdHomeomorph` of the level
of the product presentation with the product of the levels is a smooth diffeomorphism, for the
implicit-function atlases `TauCeti.Toric.IsDelzant.delzantLevelChartedSpace` of the three levels. -/
def delzantLevelProdDiffeomorph :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
    delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c') ≃ₘ⟮
      𝓘(ℝ, Fin (Fintype.card (ι ⊕ ι') + finrank ℝ (V × V')) → ℝ),
      𝓘(ℝ, Fin (Fintype.card ι + finrank ℝ V) → ℝ).prod
        𝓘(ℝ, Fin (Fintype.card ι' + finrank ℝ V') → ℝ)⟯
      delzantLevel i u c × delzantLevel i' u' c' :=
  letI := hΔ.delzantLevelChartedSpace hi
  letI := hΔ'.delzantLevelChartedSpace hi'
  letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
  -- Both maps are restrictions of the linear splitting of coordinates and of its inverse, read
  -- through the inclusions of the levels.
  { toEquiv := (delzantLevelProdHomeomorph i i' u u' c c').toEquiv
    contMDiff_toFun := by
      have hcoe := (hΔ.prod hi.injective hi'.injective hΔ').contMDiff_coe_delzantLevel
        (hi.prod hi') (m := ∞)
      refine ContMDiff.prodMk ?_ ?_
      · convert hΔ.contMDiff_codRestrict_delzantLevel hi
          (((ContinuousLinearMap.fst ℝ _ _).comp
            (sumCoordEquiv ι ι').toContinuousLinearMap).contDiff.contMDiff.comp hcoe)
          (fun x ↦ by simpa using (delzantLevelProdHomeomorph i i' u u' c c' x).1.property)
          using 1
        exact funext fun x ↦ Subtype.ext (coe_delzantLevelProdHomeomorph_fst x)
      · convert hΔ'.contMDiff_codRestrict_delzantLevel hi'
          (((ContinuousLinearMap.snd ℝ _ _).comp
            (sumCoordEquiv ι ι').toContinuousLinearMap).contDiff.contMDiff.comp hcoe)
          (fun x ↦ by simpa using (delzantLevelProdHomeomorph i i' u u' c c' x).2.property)
          using 1
        exact funext fun x ↦ Subtype.ext (coe_delzantLevelProdHomeomorph_snd x)
    contMDiff_invFun := by
      have hcoe := ((hΔ.contMDiff_coe_delzantLevel hi (m := ∞)).comp contMDiff_fst).prodMk_space
        ((hΔ'.contMDiff_coe_delzantLevel hi' (m := ∞)).comp contMDiff_snd)
      convert (hΔ.prod hi.injective hi'.injective hΔ').contMDiff_codRestrict_delzantLevel
        (hi.prod hi') ((sumCoordEquiv ι ι').symm.toContinuousLinearMap.contDiff.contMDiff.comp hcoe)
        (fun y ↦ by simp) using 1
      exact funext fun y ↦ Subtype.ext (by simp) }

@[simp]
theorem coe_delzantLevelProdDiffeomorph :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
    ⇑(hΔ.delzantLevelProdDiffeomorph hΔ' hi hi') = delzantLevelProdHomeomorph i i' u u' c c' :=
  (rfl)

@[simp]
theorem coe_delzantLevelProdDiffeomorph_symm :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
    ⇑(hΔ.delzantLevelProdDiffeomorph hΔ' hi hi').symm =
      (delzantLevelProdHomeomorph i i' u u' c c').symm :=
  (rfl)

/-- **The Delzant quotient of a product is diffeomorphic to the product of the Delzant
quotients.** For Delzant presentations in integral lattices, the homeomorphism
`TauCeti.Toric.DelzantQuotient.prodHomeomorph` is a smooth diffeomorphism
`M_(Δ × Δ') ≃ M_Δ × M_Δ'`, for the quotient manifold atlases
`TauCeti.Toric.IsDelzant.delzantQuotientChartedSpace` of the three Delzant quotients. -/
def delzantQuotientProdDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
    DelzantQuotient (i.prodMap i') (prodNormal u u') (Sum.elim c c') ≃ₘ⟮
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra (i.prodMap i') (prodNormal u u'))
        (Fin (Fintype.card (ι ⊕ ι') + finrank ℝ (V × V')) → ℝ)),
      𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i u)
          (Fin (Fintype.card ι + finrank ℝ V) → ℝ)).prod
        𝓘(ℝ, ProperSMul.QuotientModelSpace (kernelTorusLieAlgebra i' u')
          (Fin (Fintype.card ι' + finrank ℝ V') → ℝ))⟯
      DelzantQuotient i u c × DelzantQuotient i' u' c' :=
  letI := hΔ.delzantLevelChartedSpace hi
  letI := hΔ'.delzantLevelChartedSpace hi'
  letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
  letI := hΔ.delzantQuotientChartedSpace hi
  letI := hΔ'.delzantQuotientChartedSpace hi'
  letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
  haveI := hΔ.isManifold_delzantLevel hi ∞
  haveI := hΔ'.isManifold_delzantLevel hi' ∞
  haveI := hΔ.isManifold_delzantQuotient hi
  haveI := hΔ'.isManifold_delzantQuotient hi'
  -- Both maps are smooth after composing with the projections from the levels, which are
  -- surjective submersions: the composites are the projections composed with the smooth
  -- identification of the levels and with its inverse.
  { toEquiv := (DelzantQuotient.prodHomeomorph i i' u u' c c').toEquiv
    contMDiff_toFun := by
      refine (((hΔ.prod hi.injective hi'.injective hΔ').isSubmersion_delzantQuotientMk
        (hi.prod hi')).contMDiff_comp_iff DelzantQuotient.mk_surjective le_rfl).1 ?_
      convert ((hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.prodMap
        (hΔ'.isSubmersion_delzantQuotientMk hi').contMDiff).comp
          (hΔ.delzantLevelProdDiffeomorph hΔ' hi hi').contMDiff using 1
      exact funext fun x ↦ DelzantQuotient.prodHomeomorph_mk x
    contMDiff_invFun := by
      refine (((hΔ.isSubmersion_delzantQuotientMk hi).prodMap
        (hΔ'.isSubmersion_delzantQuotientMk hi')).contMDiff_comp_iff
          (DelzantQuotient.mk_surjective.prodMap DelzantQuotient.mk_surjective) le_rfl).1 ?_
      convert ((hΔ.prod hi.injective hi'.injective hΔ').isSubmersion_delzantQuotientMk
        (hi.prod hi')).contMDiff.comp (hΔ.delzantLevelProdDiffeomorph hΔ' hi hi').symm.contMDiff
        using 1
      exact funext fun y ↦ DelzantQuotient.prodHomeomorph_symm_mk y.1 y.2 }

@[simp]
theorem coe_delzantQuotientProdDiffeomorph :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
    ⇑(hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi') = DelzantQuotient.prodHomeomorph i i' u u' c c'
    :=
  (rfl)

@[simp]
theorem coe_delzantQuotientProdDiffeomorph_symm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
    ⇑(hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi').symm =
      (DelzantQuotient.prodHomeomorph i i' u u' c c').symm :=
  (rfl)

/-! ### The symplectic forms -/

/-- **The level of a product carries the product of the restricted forms.** The diffeomorphism
`delzantLevelProdDiffeomorph` of the level of the product presentation onto the product of the
levels pulls the product of the restrictions of the standard symplectic forms of `ℂ^ι` and `ℂ^ι'`
back to the restriction of the standard symplectic form of `ℂ^(ι ⊕ ι')`. -/
theorem mpullback_delzantLevelProdDiffeomorph_prod :
    letI := hΔ.delzantLevelChartedSpace hi
    letI := hΔ'.delzantLevelChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
    haveI := hΔ.isManifold_delzantLevel hi ∞
    haveI := hΔ'.isManifold_delzantLevel hi' ∞
    haveI := (hΔ.prod hi.injective hi'.injective hΔ').isManifold_delzantLevel (hi.prod hi') ∞
    SmoothForm.mpullback (hΔ.delzantLevelProdDiffeomorph hΔ' hi hi')
        (hΔ.delzantLevelProdDiffeomorph hΔ' hi hi').contMDiff
        (SmoothTwoForm.prod
          (SmoothForm.mpullback
            ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
            (hΔ.contMDiff_coe_delzantLevel hi) stdSymplecticForm.constSmooth)
          (SmoothForm.mpullback
            ((↑) : delzantLevel i' u' c' → EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι')
            (hΔ'.contMDiff_coe_delzantLevel hi') stdSymplecticForm.constSmooth)) =
      SmoothForm.mpullback
        ((↑) : delzantLevel (i.prodMap i') (prodNormal u u') (Sum.elim c c') →
          EuclideanSpace ℝ (ι ⊕ ι') × EuclideanSpace ℝ (ι ⊕ ι'))
        ((hΔ.prod hi.injective hi'.injective hΔ').contMDiff_coe_delzantLevel (hi.prod hi'))
        stdSymplecticForm.constSmooth := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ'.delzantLevelChartedSpace hi'
  let _ := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ'.isManifold_delzantLevel hi' ∞
  have := (hΔ.prod hi.injective hi'.injective hΔ').isManifold_delzantLevel (hi.prod hi') ∞
  have hcoe := (hΔ.prod hi.injective hi'.injective hΔ').contMDiff_coe_delzantLevel (hi.prod hi')
    (m := ∞)
  -- Each part of the level of the product, read in `ℂ^ι` or `ℂ^ι'`, is the corresponding part of
  -- the splitting of the coordinates of `ℂ^(ι ⊕ ι')`.
  rw [SmoothTwoForm.prod_def, map_add, SmoothForm.mpullback_mpullback _ Prod.fst,
    SmoothForm.mpullback_mpullback _ Prod.snd,
    SmoothForm.mpullback_mpullback_of_comp_eq
      (g := ((↑) : delzantLevel i u c → EuclideanSpace ℝ ι × EuclideanSpace ℝ ι))
      (contMDiff_fst.comp (hΔ.delzantLevelProdDiffeomorph hΔ' hi hi').contMDiff)
      (hΔ.contMDiff_coe_delzantLevel hi) hcoe
      ((ContinuousLinearMap.fst ℝ _ _).comp
        (sumCoordEquiv ι ι').toContinuousLinearMap).contDiff.contMDiff
      (funext fun x ↦ coe_delzantLevelProdHomeomorph_fst x),
    SmoothForm.mpullback_mpullback_of_comp_eq
      (g := ((↑) : delzantLevel i' u' c' → EuclideanSpace ℝ ι' × EuclideanSpace ℝ ι'))
      (contMDiff_snd.comp (hΔ.delzantLevelProdDiffeomorph hΔ' hi hi').contMDiff)
      (hΔ'.contMDiff_coe_delzantLevel hi') hcoe
      ((ContinuousLinearMap.snd ℝ _ _).comp
        (sumCoordEquiv ι ι').toContinuousLinearMap).contDiff.contMDiff
      (funext fun x ↦ coe_delzantLevelProdHomeomorph_snd x),
    ← map_add, mpullback_fst_sumCoordEquiv_add_mpullback_snd_sumCoordEquiv]

/-- **The Delzant quotient of a product is the symplectic product of the Delzant quotients.** The
diffeomorphism `M_(Δ × Δ') ≃ M_Δ × M_Δ'` of `delzantQuotientProdDiffeomorph` pulls the product
form `ω_Δ ⊕ ω_Δ'` of the symplectic forms of the two Delzant quotients back to the symplectic form
`ω_(Δ × Δ')` of the Delzant quotient of the product presentation. -/
theorem mpullback_delzantQuotientProdDiffeomorph_prod :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ'.isManifold_delzantQuotient hi'
    haveI := (hΔ.prod hi.injective hi'.injective hΔ').isManifold_delzantQuotient (hi.prod hi')
    SmoothForm.mpullback (hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi')
        (hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi').contMDiff
        (SmoothTwoForm.prod (hΔ.delzantQuotientSymplecticForm hi)
          (hΔ'.delzantQuotientSymplecticForm hi')) =
      (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientSymplecticForm (hi.prod hi') := by
  let _ := hΔ.delzantLevelChartedSpace hi
  let _ := hΔ'.delzantLevelChartedSpace hi'
  let _ := (hΔ.prod hi.injective hi'.injective hΔ').delzantLevelChartedSpace (hi.prod hi')
  let _ := hΔ.delzantQuotientChartedSpace hi
  let _ := hΔ'.delzantQuotientChartedSpace hi'
  let _ := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
  have := hΔ.isManifold_delzantLevel hi ∞
  have := hΔ'.isManifold_delzantLevel hi' ∞
  have := (hΔ.prod hi.injective hi'.injective hΔ').isManifold_delzantLevel (hi.prod hi') ∞
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ'.isManifold_delzantQuotient hi'
  have := (hΔ.prod hi.injective hi'.injective hΔ').isManifold_delzantQuotient (hi.prod hi')
  -- Both forms are determined by their pullbacks to the level of the product, where the
  -- projection followed by the product diffeomorphism is the product of the projections composed
  -- with the identification of the levels.
  rw [(hΔ.prod hi.injective hi'.injective hΔ').eq_delzantQuotientSymplecticForm_iff (hi.prod hi'),
    SmoothForm.mpullback_mpullback_of_comp_eq
      ((hΔ.prod hi.injective hi'.injective hΔ').isSubmersion_delzantQuotientMk
        (hi.prod hi')).contMDiff
      (hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi').contMDiff
      (hΔ.delzantLevelProdDiffeomorph hΔ' hi hi').contMDiff
      ((hΔ.isSubmersion_delzantQuotientMk hi).contMDiff.prodMap
        (hΔ'.isSubmersion_delzantQuotientMk hi').contMDiff)
      (funext fun x ↦ DelzantQuotient.prodHomeomorph_mk x),
    SmoothTwoForm.mpullback_prodMap_prod (hΔ.isSubmersion_delzantQuotientMk hi).contMDiff
      (hΔ'.isSubmersion_delzantQuotientMk hi').contMDiff,
    hΔ.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm hi,
    hΔ'.mpullback_delzantQuotientMk_delzantQuotientSymplecticForm hi',
    hΔ.mpullback_delzantLevelProdDiffeomorph_prod hΔ' hi hi']

/-- The inverse diffeomorphism `M_Δ × M_Δ' ≃ M_(Δ × Δ')` pulls the symplectic form of the Delzant
quotient of the product presentation back to the product form `ω_Δ ⊕ ω_Δ'`. -/
theorem mpullback_delzantQuotientProdDiffeomorph_symm_delzantQuotientSymplecticForm :
    letI := hΔ.delzantQuotientChartedSpace hi
    letI := hΔ'.delzantQuotientChartedSpace hi'
    letI := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
    haveI := hΔ.isManifold_delzantQuotient hi
    haveI := hΔ'.isManifold_delzantQuotient hi'
    haveI := (hΔ.prod hi.injective hi'.injective hΔ').isManifold_delzantQuotient (hi.prod hi')
    SmoothForm.mpullback (hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi').symm
        (hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi').symm.contMDiff
        ((hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientSymplecticForm (hi.prod hi')) =
      SmoothTwoForm.prod (hΔ.delzantQuotientSymplecticForm hi)
        (hΔ'.delzantQuotientSymplecticForm hi') := by
  let _ := hΔ.delzantQuotientChartedSpace hi
  let _ := hΔ'.delzantQuotientChartedSpace hi'
  let _ := (hΔ.prod hi.injective hi'.injective hΔ').delzantQuotientChartedSpace (hi.prod hi')
  have := hΔ.isManifold_delzantQuotient hi
  have := hΔ'.isManifold_delzantQuotient hi'
  have := (hΔ.prod hi.injective hi'.injective hΔ').isManifold_delzantQuotient (hi.prod hi')
  rw [← hΔ.mpullback_delzantQuotientProdDiffeomorph_prod hΔ' hi hi',
    SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_id contMDiff_id
      (funext (hΔ.delzantQuotientProdDiffeomorph hΔ' hi hi').apply_symm_apply),
    SmoothForm.mpullback_id, LinearMap.id_apply, LinearMap.id_apply]

end IsDelzant

end TauCeti.Toric
