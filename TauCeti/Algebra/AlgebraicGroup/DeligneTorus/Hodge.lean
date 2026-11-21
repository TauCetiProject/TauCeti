/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.BaseChange
public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# The Hodge decomposition of a representation of the Deligne torus

A representation of the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ` on a real vector space `V` is a right
comodule over the coordinate Hopf algebra `S`. Its complexification `ℂ ⊗[ℝ] V` splits into the
subspaces

```text
V^{p,q} = { v | h(z₁, z₂) v = z₁ ^ (-p) * z₂ ^ (-q) • v },
```

where `(z₁, z₂)` are the coordinates of a point of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ`
(`TauCeti.DeligneTorus.complexSplitting`). This is the homology sign convention: a real point
`z ∈ S(ℝ) = ℂˣ` has coordinates `(z, conj z)` and acts on `V^{p,q}` by `z ^ (-p) * conj z ^ (-q)`,
and the weight `w(r)` acts on `V^{p,q}` by `r ^ (p + q)`.

The subspace `V^{p,q}` is defined as a weight space of the comodule `ℂ ⊗[ℝ] V` over
`ℂ ⊗[ℝ] S ≅ ℂ[ℤ²]` (`TauCeti.DeligneTorus.splittingBialgEquiv`). The general weight
decomposition of comodules over a group algebra then makes `ℂ ⊗[ℝ] V` the direct sum of the
`V^{p,q}`. Complex conjugation of `ℂ ⊗[ℝ] V` exchanges `V^{p,q}` and `V^{q,p}`, because on
coordinate rings it is the automorphism `TauCeti.DeligneTorus.conjSwap` of `ℂ[ℤ²]`, which fixes the
splitting. Consequently, when `V` is finite-dimensional and every nonzero `V^{p,q}` has `p + q = n`,
the family `p ↦ V^{p, n - p}` is a Hodge decomposition of weight `n`. Then
`TauCeti.Hodge.HodgeStructureOn.ofDecomposition` turns `V` into a real Hodge structure of
weight `n`.

## Main definitions

* `TauCeti.DeligneTorus.hodgeComponent V p q`: the subspace `V^{p,q}` of `ℂ ⊗[ℝ] V`.

## Main results

* `TauCeti.DeligneTorus.endOfPoint_rTensor_of_mem_hodgeComponent`: a point `g` of `S` with
  values in a complex algebra acts on `V^{p,q}` by the character `(-p, -q)` of `g`. For complex
  points this is `TauCeti.DeligneTorus.endOfPoint_of_mem_hodgeComponent`, for real points
  `TauCeti.DeligneTorus.endOfPoint_real_of_mem_hodgeComponent`, and for the weight
  `TauCeti.DeligneTorus.endOfPoint_weight_of_mem_hodgeComponent`.
* `TauCeti.DeligneTorus.mem_hodgeComponent_iff`: `V^{p,q}` is cut out by the action of the
  universal point of `𝔾ₘ × 𝔾ₘ`.
* `TauCeti.DeligneTorus.isInternal_hodgeComponent`: `ℂ ⊗[ℝ] V` is the internal direct sum of the
  `V^{p,q}`.
* `TauCeti.DeligneTorus.finite_setOf_hodgeComponent_ne_bot`: a finite-dimensional
  representation has finitely many nonzero `V^{p,q}`.
* `TauCeti.DeligneTorus.conj_mem_hodgeComponent`, `TauCeti.DeligneTorus.map_conj_hodgeComponent`:
  complex conjugation carries `V^{p,q}` onto `V^{q,p}`.
* `TauCeti.DeligneTorus.isHodgeDecomposition_hodgeComponent`: for a finite-dimensional
  representation pure of weight `n`, the family `p ↦ V^{p, n - p}` is a Hodge decomposition of
  weight `n`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
* P. Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389 (1971), §1.
* P. Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §1.2.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

variable (V : Type*) [AddCommGroup V] [Module ℝ V] [Comodule ℝ S V]

/-- **The Hodge component `V^{p,q}`** of a real representation `V` of the Deligne torus: the
subspace of `ℂ ⊗[ℝ] V` on which a point of `S_ℂ ≅ 𝔾ₘ × 𝔾ₘ` with coordinates `(z₁, z₂)` acts by
`z₁ ^ (-p) * z₂ ^ (-q)` (`endOfPoint_rTensor_of_mem_hodgeComponent`). It is the weight space of
the character `(-p, -q)` of the complexified comodule. -/
noncomputable def hodgeComponent (p q : ℤ) : Submodule ℂ (ℂ ⊗[ℝ] V) :=
  letI := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
  DiagonalizableGroup.weightSpace (R := ℂ) (C := ℂ ⊗[ℝ] S) (ℂ ⊗[ℝ] V)
    ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
      ℂ ⊗[ℝ] S →ₗc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
    (Multiplicative.ofAdd (-p, -q))

/-- `V^{p,q}` is the weight space of the character `(-p, -q)` of the comodule `ℂ ⊗[ℝ] V` over
`ℂ ⊗[ℝ] S ≅ ℂ[ℤ²]`. -/
theorem hodgeComponent_def (p q : ℤ) :
    letI := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
    hodgeComponent V p q =
      DiagonalizableGroup.weightSpace (R := ℂ) (C := ℂ ⊗[ℝ] S) (ℂ ⊗[ℝ] V)
        ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
          ℂ ⊗[ℝ] S →ₗc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
        (Multiplicative.ofAdd (-p, -q)) :=
  (rfl)

variable {V}

/-! ### The action of points -/

section Points

-- The real structure of `R` is the one induced from `ℂ`, so that `R ⊗[ℝ] V` carries a single
-- real module structure on `R`.
variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- **A point of `S` acts on `V^{p,q}` by the character `(-p, -q)`.** For a point `g` of `S`
with values in a complex algebra `R`, with coordinates `(z₁, z₂)` in `S(R) ≃ Rˣ × Rˣ`, and for
`v ∈ V^{p,q}`, the action of `g` on the image of `v` in `R ⊗[ℝ] V` is multiplication by
`z₁ ^ (-p) * z₂ ^ (-q)`. -/
theorem endOfPoint_rTensor_of_mem_hodgeComponent (g : WithConv (S →ₐ[ℝ] R)) {p q : ℤ}
    {v : ℂ ⊗[ℝ] V} (hv : v ∈ hodgeComponent V p q) :
    Comodule.endOfPoint V g.ofConv
        (LinearMap.rTensor V (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v) =
      (characterGroup R (.ofAdd (-p, -q)) g : R) •
        LinearMap.rTensor V (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v := by
  let _ := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
  let χ : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐ[ℂ] R :=
    (AlgHom.liftEquiv ℝ ℂ S R g.ofConv).comp
      (splittingBialgEquiv.symm : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐ[ℂ] ℂ ⊗[ℝ] S)
  have hχ :
      χ.comp ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
        _ →ₐ[ℂ] _) = AlgHom.liftEquiv ℝ ℂ S R g.ofConv :=
    AlgHom.ext fun x ↦ by simp [χ]
  have hχ' : χ (MonoidAlgebra.single (Multiplicative.ofAdd (-p, -q)) 1) =
      characterGroup R (.ofAdd (-p, -q)) g := by
    simp [χ, liftEquiv_splittingBialgEquiv_symm_single, -splittingBialgEquiv_symm_single]
  have h := DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace (C := ℂ ⊗[ℝ] S) (ℂ ⊗[ℝ] V)
    (splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) χ 1
    ((hodgeComponent_def V p q).le hv)
  rw [hχ, one_mul, hχ'] at h
  have h' := congrArg (TensorProduct.AlgebraTensorModule.cancelBaseChange ℝ ℂ R R V) h
  rwa [Comodule.cancelBaseChange_endOfPoint_liftEquiv,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul_eq_smul_rTensor,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul_eq_smul_rTensor, one_smul] at h'

/-- **A complex point of `S` acts on `V^{p,q}` by the character `(-p, -q)`**: a point `g` of
`S(ℂ) ≃ ℂˣ × ℂˣ` with coordinates `(z₁, z₂)` acts on `V^{p,q}` by `z₁ ^ (-p) * z₂ ^ (-q)`. -/
theorem endOfPoint_of_mem_hodgeComponent (g : WithConv (S →ₐ[ℝ] ℂ)) {p q : ℤ}
    {v : ℂ ⊗[ℝ] V} (hv : v ∈ hodgeComponent V p q) :
    Comodule.endOfPoint V g.ofConv v = (characterGroup ℂ (.ofAdd (-p, -q)) g : ℂ) • v := by
  have h := endOfPoint_rTensor_of_mem_hodgeComponent g hv
  have hid : (IsScalarTower.toAlgHom ℝ ℂ ℂ).toLinearMap = LinearMap.id :=
    LinearMap.ext fun _ ↦ by simp
  rwa [hid, LinearMap.rTensor_id, LinearMap.id_apply] at h

/-- **A real point `z ∈ S(ℝ) = ℂˣ` acts on `V^{p,q}` by `z ^ (-p) * conj z ^ (-q)`.** This is the
homology sign convention for the Hodge types of a representation of the Deligne torus. -/
theorem endOfPoint_real_of_mem_hodgeComponent (f : WithConv (S →ₐ[ℝ] ℝ)) {p q : ℤ}
    {v : ℂ ⊗[ℝ] V} (hv : v ∈ hodgeComponent V p q) :
    Comodule.endOfPoint V ((Algebra.ofId ℝ ℂ).comp f.ofConv) v =
      ((realPointsMulEquiv f ^ (-p) * star (realPointsMulEquiv f) ^ (-q) : ℂˣ) : ℂ) • v := by
  have h := endOfPoint_of_mem_hodgeComponent (AlgHom.mapValue (Algebra.ofId ℝ ℂ) f) hv
  rwa [characterGroup_apply, complexSplitting_real, AlgHom.mapValue_apply, ofConv_toConv] at h

/-- **The weight `w(r)` acts on `V^{p,q}` by `r ^ (p + q)`.** -/
theorem endOfPoint_weight_of_mem_hodgeComponent (r : Rˣ) {p q : ℤ} {v : ℂ ⊗[ℝ] V}
    (hv : v ∈ hodgeComponent V p q) :
    Comodule.endOfPoint V (weight R r).ofConv
        (LinearMap.rTensor V (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v) =
      ((r ^ (p + q) : Rˣ) : R) •
        LinearMap.rTensor V (IsScalarTower.toAlgHom ℝ ℂ R).toLinearMap v := by
  rw [endOfPoint_rTensor_of_mem_hodgeComponent _ hv, characterGroup_weight, neg_add, neg_neg,
    neg_neg]

/-- **`V^{p,q}` is cut out by the universal point of `𝔾ₘ × 𝔾ₘ`**: `v` lies in `V^{p,q}` exactly
when the coordinate point `splittingPoint` of `S` with values in `ℂ[ℤ²]` acts on the image of `v`
in `ℂ[ℤ²] ⊗[ℝ] V` by multiplication by `X^{(-p,-q)}`. -/
theorem mem_hodgeComponent_iff {p q : ℤ} {v : ℂ ⊗[ℝ] V} :
    v ∈ hodgeComponent V p q ↔
      Comodule.endOfPoint V splittingPoint.ofConv
          (LinearMap.rTensor V
            (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap v) =
        MonoidAlgebra.single (Multiplicative.ofAdd (-p, -q)) (1 : ℂ) •
          LinearMap.rTensor V
            (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap
            v := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · rw [endOfPoint_rTensor_of_mem_hodgeComponent _ hv, characterGroup_splittingPoint]
  · let _ := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
    have hiff := DiagonalizableGroup.mem_weightSpace_iff_endOfPoint (R := ℂ) (C := ℂ ⊗[ℝ] S)
      (ℂ ⊗[ℝ] V) (splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
      (Multiplicative.ofAdd (-p, -q)) v
    -- match the projections in `hiff` with the coercions in `hodgeComponent_def`
    have hcoalg : BialgHom.toCoalgHom
        (splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) =
          ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
            _ →ₗc[ℂ] _) :=
      CoalgHom.ext fun x ↦ by rw [BialgHom.toCoalgHom_apply, BialgHom.coe_toCoalgHom]
    have halg :
        (splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))).toAlgHom =
          AlgHom.liftEquiv ℝ ℂ S _ splittingPoint.ofConv :=
      AlgHom.ext fun x ↦ by simp [← splittingBialgEquiv_toAlgHom]
    rw [hcoalg, ← hodgeComponent_def, halg] at hiff
    refine hiff.mpr ?_
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange ℝ ℂ
      (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
      V).injective
    rw [Comodule.cancelBaseChange_endOfPoint_liftEquiv,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul_eq_smul_rTensor,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul_eq_smul_rTensor, one_smul]
    exact hv

end Points

/-! ### The Hodge decomposition -/

/-- The indexing of the Hodge components by the characters of `𝔾ₘ × 𝔾ₘ`: `V^{p,q}` is the weight
space of the character `(-p, -q)`. -/
private def hodgeIndexEquiv : ℤ × ℤ ≃ Multiplicative (ℤ × ℤ) :=
  (Equiv.neg (ℤ × ℤ)).trans Multiplicative.ofAdd

private theorem hodgeComponent_eq_comp :
    letI := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
    (fun pq : ℤ × ℤ ↦ hodgeComponent V pq.1 pq.2) =
      DiagonalizableGroup.weightSpace (R := ℂ) (C := ℂ ⊗[ℝ] S) (ℂ ⊗[ℝ] V)
        ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
          _ →ₗc[ℂ] _) ∘ hodgeIndexEquiv :=
  funext fun pq ↦ hodgeComponent_def V pq.1 pq.2

variable (V) in
/-- **The Hodge decomposition of a representation of `S`**: `ℂ ⊗[ℝ] V` is the internal direct sum
of the Hodge components `V^{p,q}`. -/
theorem isInternal_hodgeComponent :
    DirectSum.IsInternal fun pq : ℤ × ℤ ↦ hodgeComponent V pq.1 pq.2 := by
  let _ := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
  have h := DiagonalizableGroup.isInternal_weightSpace (R := ℂ) (C := ℂ ⊗[ℝ] S) (ℂ ⊗[ℝ] V)
    ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
      ℂ ⊗[ℝ] S →ₗc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
  -- the weight decomposition is stated with classical decidable equality on the characters
  let _ : DecidableEq (Multiplicative (ℤ × ℤ)) := Classical.decEq _
  rw [hodgeComponent_eq_comp]
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (h.submodule_iSupIndep.comp hodgeIndexEquiv.injective)
    ((hodgeIndexEquiv.surjective.iSup_comp _).trans h.submodule_iSup_eq_top)

variable (V) in
/-- **A finite-dimensional representation of `S` has only finitely many nonzero Hodge
components.** -/
theorem finite_setOf_hodgeComponent_ne_bot [Module.Finite ℝ V] :
    {pq : ℤ × ℤ | hodgeComponent V pq.1 pq.2 ≠ ⊥}.Finite := by
  let _ := Comodule.baseChange (R := ℝ) (H := S) (M := V) ℂ
  have h := DiagonalizableGroup.finite_setOf_weightSpace_ne_bot (R := ℂ) (C := ℂ ⊗[ℝ] S) (ℂ ⊗[ℝ] V)
    ((splittingBialgEquiv : ℂ ⊗[ℝ] S →ₐc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ))) :
      ℂ ⊗[ℝ] S →ₗc[ℂ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))
  change ((fun pq : ℤ × ℤ ↦ hodgeComponent V pq.1 pq.2) ⁻¹' {W | W ≠ ⊥}).Finite
  rw [hodgeComponent_eq_comp, Set.preimage_comp]
  exact h.preimage hodgeIndexEquiv.injective.injOn

/-! ### Complex conjugation -/

/-- **Complex conjugation maps `V^{p,q}` into `V^{q,p}`.** -/
theorem conj_mem_hodgeComponent {p q : ℤ} {v : ℂ ⊗[ℝ] V} (hv : v ∈ hodgeComponent V p q) :
    (Hodge.complexificationConjugation V).toEquiv v ∈ hodgeComponent V q p := by
  let τ : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) →ₐ[ℝ] MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) :=
    conjSwap
  let ι := (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap
  -- conjugation of `ℂ ⊗[ℝ] V` becomes `conjSwap` on `ℂ[ℤ²] ⊗[ℝ] V`
  have hι (w : ℂ ⊗[ℝ] V) : LinearMap.rTensor V ι ((Hodge.complexificationConjugation V).toEquiv w) =
      LinearMap.rTensor V τ.toLinearMap (LinearMap.rTensor V ι w) := by
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul c x => simp [ι, τ]
  -- `conjSwap` commutes with the action of `splittingPoint`, which it fixes
  have hτ (y : MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)) ⊗[ℝ] V) :
      Comodule.endOfPoint V splittingPoint.ofConv (LinearMap.rTensor V τ.toLinearMap y) =
        LinearMap.rTensor V τ.toLinearMap (Comodule.endOfPoint V splittingPoint.ofConv y) := by
    have h := LinearMap.congr_fun
      (Comodule.rTensor_comp_endOfPoint V τ splittingPoint.ofConv) y
    rw [conjSwap_comp_splittingPoint] at h
    exact h.symm
  rw [mem_hodgeComponent_iff] at hv ⊢
  rw [hι, hτ, hv, AlgHom.rTensor_toLinearMap_apply_smul]
  simp [τ, ι]

/-- **Complex conjugation carries `V^{p,q}` onto `V^{q,p}`.** -/
@[simp]
theorem map_conj_hodgeComponent (p q : ℤ) :
    (hodgeComponent V p q).map (Hodge.complexificationConjugation V).toEquiv.toLinearMap =
      hodgeComponent V q p := by
  refine le_antisymm ?_ fun v hv ↦ ⟨(Hodge.complexificationConjugation V).toEquiv v,
    conj_mem_hodgeComponent hv, Hodge.Conjugation.apply_apply _ v⟩
  rintro _ ⟨v, hv, rfl⟩
  exact conj_mem_hodgeComponent hv

/-! ### Representations pure of one weight -/

/-- **A pure representation of `S` is a real Hodge structure.** If `V` is finite-dimensional and
every nonzero Hodge component `V^{p,q}` has `p + q = n`, then the components `p ↦ V^{p, n - p}`
form a Hodge decomposition of weight `n` of `ℂ ⊗[ℝ] V`. The corresponding pure Hodge structure is
`TauCeti.Hodge.HodgeStructureOn.ofDecomposition`. -/
theorem isHodgeDecomposition_hodgeComponent [Module.Finite ℝ V] {n : ℤ}
    (hV : ∀ p q, p + q ≠ n → hodgeComponent V p q = ⊥) :
    Hodge.IsHodgeDecomposition (Hodge.complexificationConjugation V) n
      fun p ↦ hodgeComponent V p (n - p) where
  isInternal := by
    have h := isInternal_hodgeComponent V
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
    refine ⟨h.1.comp (f := fun p : ℤ ↦ (p, n - p)) fun p p' hp ↦ congrArg Prod.fst hp,
      eq_top_iff.2 (h.2 ▸ iSup_le fun pq ↦ ?_)⟩
    by_cases hpq : pq.1 + pq.2 = n
    · exact le_iSup_of_le pq.1 (by rw [show pq.2 = n - pq.1 by omega])
    · rw [hV _ _ hpq]
      exact bot_le
  map_conj p := by rw [map_conj_hodgeComponent, sub_sub_cancel]
  exists_forall_lt_eq_bot := by
    obtain ⟨a, ha⟩ := ((finite_setOf_hodgeComponent_ne_bot V).image Prod.fst).bddBelow
    exact ⟨a, fun p hp ↦ by_contra fun h ↦ (ha ⟨(p, n - p), h, rfl⟩).not_gt hp⟩

end TauCeti.DeligneTorus
