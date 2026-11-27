/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Connected
public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.MumfordTate.Stabilizer
public import TauCeti.Algebra.AlgebraicGroup.Reductive.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer.Subgroup
public import TauCeti.Geometry.Hodge.MumfordTate.HodgeComponent
public import TauCeti.Geometry.Hodge.Orthogonal

/-!
# Reductivity of the Mumford–Tate group of a polarizable Hodge structure

Let `V` be a rational Hodge structure, pure of weight `n`, with a basis `b` of `V_ℚ`, so that
`GL_V ≅ GL_d`. Its Mumford–Tate group `MT(V) ⊆ GL_d` is the smallest closed `ℚ`-subgroup through
whose real extension `h_V : S → GL_{d,ℝ}` factors
(`TauCeti.Hodge.HodgeStructureOn.mumfordTateHopfIdeal`). This file proves:

* the rational subspaces of `V_ℚ` stable under `MT(V)` are exactly the rational sub-Hodge
  structures, which is
  `TauCeti.Hodge.HodgeStructureOn.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_piece`
* if `V` is polarizable, `MT(V)` is reductive, which is
  `TauCeti.Hodge.HodgeStructureOn.reductiveCommHopfAlgProperty_quotient_mumfordTateHopfIdeal`.

The first statement specializes the one for an arbitrary homomorphism from the Deligne torus
(`TauCeti.DeligneTorus.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_hodgeComponent`)
to `h_V`. The identification `ℝ ⊗[ℚ] ℚ^d ≃ ℝ^d` is a morphism of representations of `S`
(`TauCeti.Hodge.HodgeStructureOn.realComoduleHom`), and the Hodge components of `ℝ^d` are those
of `V` (`TauCeti.Hodge.HodgeStructureOn.hodgeComponent_corestrictStandardComodule`).

For reductivity, `MT(V)` is geometrically connected
(`TauCeti.DeligneTorus.geometricallyConnectedCommHopfAlgProperty_quotient_mumfordTateHopfIdeal`),
so it is reductive exactly when its standard representation on `ℚ^d` is completely reducible
(`TauCeti.reductiveCommHopfAlgProperty_iff_isCompletelyReducible_corestrictStandardComodule`).
An `MT(V)`-stable subspace is a rational sub-Hodge structure, a polarization gives it a
complementary rational sub-Hodge structure (`TauCeti.Hodge.exists_isCompl_of_isPolarizable`), and
that complement is again `MT(V)`-stable.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16).
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), Proposition 3.6,
  pp. 24–25.
-/

public section

open CategoryTheory TauCeti.DeligneTorus TauCeti.GeneralLinear
open scoped TensorProduct

namespace TauCeti.Hodge.HodgeStructureOn

variable {Vℤ Vℚ Vℂ : Type*} [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
  [AddCommGroup Vℂ] [Module ℂ Vℂ] {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
  (hℚ : IsBaseChange ℚ ιℚ) {hℂ : IsBaseChange ℂ ιℂ} {n : ℤ} {d : ℕ}
  (b : Module.Basis (Fin d) ℚ Vℚ) (hs : HodgeStructureOn Vℂ (latticeConjugation hℂ) n)

/-- The identification `ℝ ⊗[ℚ] ℚ^d ≃ ℝ^d` intertwines the coaction of `S` on the real extension
of the standard representation through `h_V` with the coaction of `S` on `ℝ^d` through
`realCoordinateBialgHom`: both send `1 ⊗ e_j` to `∑ i, e_i ⊗ h(X_{ij})`. -/
private theorem map_coact_realComodule :
    letI := standardComodule ℚ d
    TensorProduct.map (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d)).toLinearMap
        (LinearMap.id : S →ₗ[ℝ] S) ∘ₗ (realComodule (Fin d → ℚ) (hs.deligneHom hℚ b)).coact =
      (corestrictStandardComodule ℝ d
        (hs.realCoordinateBialgHom (latticeConjugation_toEquiv_rationalBasis hℚ b))).coact ∘ₗ
        (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d)).toLinearMap := by
  let _ := standardComodule ℚ d
  let _ := standardComodule ℝ d
  let _ := Comodule.baseChange (R := ℚ) (H := coordinateHopfAlgebra ℚ d) (M := Fin d → ℚ) ℝ
  have hsingle (i : Fin d) :
      TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d) (1 ⊗ₜ Pi.single i 1) = Pi.single i 1 := by
    ext k
    simp [Pi.single_apply]
  refine TensorProduct.AlgebraTensorModule.curry_injective <| LinearMap.ext_ring <|
    (Pi.basisFun ℚ (Fin d)).ext fun j ↦ ?_
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [realComodule_def, Comodule.corestrict_coact_apply, Comodule.baseChange_coact,
    Comodule.baseChangeCoact_tmul, corestrictStandardComodule, Comodule.corestrict_coact_apply]
  simp only [Pi.basisFun_apply, standardComodule_coact, standardCoact_apply_basisFun,
    map_sum, TensorProduct.tmul_sum, hsingle,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul,
    LinearMap.id_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearEquiv.coe_coe, hsingle]
  congr 1
  exact hs.deligneHom_one_tmul_X hℚ b i j

/-- **The real representation of `S` of a rational Hodge structure in coordinates.** For a basis
`b` of `V_ℚ`, the identification `ℝ ⊗[ℚ] ℚ^d ≃ ℝ^d` is a morphism of representations of `S`,
from the real extension of the standard representation of `GL_d` restricted along `h_V`
(`TauCeti.DeligneTorus.realComodule`) to `ℝ^d` with `S` acting through
`TauCeti.Hodge.HodgeStructureOn.realCoordinateBialgHom` in the induced basis of `V_ℂ`. -/
noncomputable def realComoduleHom :
    letI := standardComodule ℚ d
    letI := realComodule (Fin d → ℚ) (hs.deligneHom hℚ b)
    letI := corestrictStandardComodule ℝ d
      (hs.realCoordinateBialgHom (latticeConjugation_toEquiv_rationalBasis hℚ b))
    Comodule.Hom ℝ S (ℝ ⊗[ℚ] (Fin d → ℚ)) (Fin d → ℝ) :=
  letI := standardComodule ℚ d
  letI := realComodule (Fin d → ℚ) (hs.deligneHom hℚ b)
  letI := corestrictStandardComodule ℝ d
    (hs.realCoordinateBialgHom (latticeConjugation_toEquiv_rationalBasis hℚ b))
  { toLinearMap := (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d)).toLinearMap
    map_coact := hs.map_coact_realComodule hℚ b }

/-- The underlying linear map of `realComoduleHom` is `ℝ ⊗[ℚ] ℚ^d ≃ ℝ^d`. -/
@[simp]
theorem realComoduleHom_toLinearMap :
    letI := standardComodule ℚ d
    letI := realComodule (Fin d → ℚ) (hs.deligneHom hℚ b)
    letI := corestrictStandardComodule ℝ d
      (hs.realCoordinateBialgHom (latticeConjugation_toEquiv_rationalBasis hℚ b))
    (hs.realComoduleHom hℚ b).toLinearMap =
      (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d)).toLinearMap :=
  (rfl)

/-- `realComoduleHom` acts as `ℝ ⊗[ℚ] ℚ^d ≃ ℝ^d`. -/
@[simp]
theorem realComoduleHom_apply (x : ℝ ⊗[ℚ] (Fin d → ℚ)) :
    letI := standardComodule ℚ d
    letI := realComodule (Fin d → ℚ) (hs.deligneHom hℚ b)
    letI := corestrictStandardComodule ℝ d
      (hs.realCoordinateBialgHom (latticeConjugation_toEquiv_rationalBasis hℚ b))
    hs.realComoduleHom hℚ b x = TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d) x :=
  (rfl)

/-- The complexification of `ℝ ⊗ W ⊆ ℝ^d`, carried to `V_ℂ` by the basis induced by `b`, is the
complexification of the image of `W` in `V_ℚ`. -/
private theorem map_tensorPiEquiv_baseChange_map_piScalarRight (W : Submodule ℚ (Fin d → ℚ)) :
    (((W.baseChange ℝ).map (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d)).toLinearMap).baseChange
        ℂ).map ((rationalBasis hℚ hℂ b).tensorPiEquiv ℝ).toLinearMap =
      rationalToComplexSubmodule hℚ hℂ (W.map b.equivFun.symm.toLinearMap) := by
  rw [rationalToComplexSubmodule_eq_span, ← W.span_eq, Submodule.baseChange_span,
    Submodule.map_span, Submodule.baseChange_span, Submodule.map_span, Submodule.span_eq,
    Submodule.map_coe, Set.image_image, Set.image_image, Set.image_image, Set.image_image]
  congr 2
  funext w
  simp only [TensorProduct.mk_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
    TensorProduct.tmul_sum, map_sum]
  rw [TensorProduct.piScalarRight_one_tmul, Module.Basis.tensorPiEquiv_tmul, one_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [rationalBasis_apply, ← rationalToComplexLinearEquiv_one_tmul hℚ hℂ,
    TensorProduct.tmul_smul, ← algebraMap_smul ℂ (w i), map_smul]
  congr 1

/-- Reindexing the Hodge components of weight `n` by the pairs `(p, q)` with `p + q = n`. -/
private theorem iSup_inf_ite_piece (A : Submodule ℂ Vℂ) :
    (⨆ pq : ℤ × ℤ, A ⊓ if pq.1 + pq.2 = n then hs.piece pq.1 else ⊥) = ⨆ p, A ⊓ hs.piece p := by
  refine le_antisymm (iSup_le fun pq ↦ ?_) (iSup_le fun p ↦ ?_)
  · split_ifs
    · exact le_iSup (fun p ↦ A ⊓ hs.piece p) pq.1
    · simp
  · refine le_iSup_of_le (p, n - p) ?_
    simp

/-- **The sub-Hodge structures are the subspaces stable under the Mumford–Tate group.** In the
coordinates given by a basis `b` of `V_ℚ`, a subspace `W ≤ ℚ^d` is stable under `MT(V)` (its
stabilizer Hopf ideal lies below the Mumford–Tate ideal) exactly when its image in `V_ℚ` is a
rational sub-Hodge structure: the complexification is the sum of its intersections with the
`H^{p,n-p}`. -/
theorem stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_piece
    (W : Submodule ℚ (Fin d → ℚ)) :
    letI := standardComodule ℚ d
    W.stabilizerHopfIdeal (coordinateHopfAlgebra ℚ d) ≤ hs.mumfordTateHopfIdeal hℚ b ↔
      rationalToComplexSubmodule hℚ hℂ (W.map b.equivFun.symm.toLinearMap) =
        ⨆ p, rationalToComplexSubmodule hℚ hℂ (W.map b.equivFun.symm.toLinearMap) ⊓
          hs.piece p := by
  let _ := standardComodule ℚ d
  let he := latticeConjugation_toEquiv_rationalBasis hℚ (hℂ := hℂ) b
  let _ := realComodule (Fin d → ℚ) (hs.deligneHom hℚ b)
  let _ := corestrictStandardComodule ℝ d (hs.realCoordinateBialgHom he)
  set E := (rationalBasis hℚ hℂ b).tensorPiEquiv ℝ with hEdef
  rw [mumfordTateHopfIdeal_eq_mumfordTateHopfIdeal_deligneHom,
    DeligneTorus.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff,
    ← Submodule.stabilizerHopfIdeal_map_of_injective (hs.realComoduleHom hℚ b)
      (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin d)).injective,
    Submodule.stabilizerHopfIdeal_eq_bot_iff_eq_iSup_inf_hodgeComponent,
    ← (Submodule.map_injective_of_injective E.injective).eq_iff]
  have hE := map_tensorPiEquiv_baseChange_map_piScalarRight hℚ (hℂ := hℂ) b W
  rw [realComoduleHom_toLinearMap, Submodule.map_iSup]
  simp_rw [Submodule.map_inf (E : ℂ ⊗[ℝ] (Fin d → ℝ) →ₗ[ℂ] Vℂ) E.injective]
  rw [hE]
  simp_rw [hs.hodgeComponent_corestrictStandardComodule he, ← hEdef]
  have hmap (pq : ℤ × ℤ) :
      (if pq.1 + pq.2 = n then (hs.piece pq.1).map E.symm.toLinearMap else ⊥).map
          E.toLinearMap =
        if pq.1 + pq.2 = n then hs.piece pq.1 else ⊥ := by
    split_ifs
    · exact (Submodule.map_symm_eq_iff E).mp rfl
    · exact Submodule.map_bot _
  simp_rw [hmap]
  rw [iSup_inf_ite_piece]

/-- **The Mumford–Tate group of a polarizable Hodge structure is reductive.** For a polarizable
rational Hodge structure `V` with a basis `b` of `V_ℚ`, the closed subgroup `MT(V) ⊆ GL_d` cut
out by `TauCeti.Hodge.HodgeStructureOn.mumfordTateHopfIdeal` is reductive. -/
theorem reductiveCommHopfAlgProperty_quotient_mumfordTateHopfIdeal (hpol : IsPolarizable hℂ hs) :
    reductiveCommHopfAlgProperty ℚ
      (FiniteTypeCommHopfAlgCat.quotient
        (⟨coordinateHopfAlgebra ℚ d,
          inferInstanceAs (Algebra.FiniteType ℚ (coordinateHopfAlgebra ℚ d))⟩ :
          FiniteTypeCommHopfAlgCat ℚ)
        (hs.mumfordTateHopfIdeal hℚ b)) := by
  have _ : Module.Finite ℚ Vℚ := Module.Finite.of_basis b
  have hconn : geometricallyConnectedCommHopfAlgProperty ℚ
      (_root_.CommHopfAlgCat.quotient (coordinateHopfAlgebra ℚ d)
        (hs.mumfordTateHopfIdeal hℚ b)) := by
    rw [mumfordTateHopfIdeal_eq_mumfordTateHopfIdeal_deligneHom]
    exact geometricallyConnectedCommHopfAlgProperty_quotient_mumfordTateHopfIdeal
      (hs.deligneHom hℚ b)
  rw [reductiveCommHopfAlgProperty_iff_isCompletelyReducible_corestrictStandardComodule _ hconn
    (_root_.CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra ℚ d)
      (hs.mumfordTateHopfIdeal hℚ b)).hom
    (_root_.CommHopfAlgCat.mkQuotient_surjective _ _)]
  let _ := standardComodule ℚ d
  refine (Comodule.isCompletelyReducible_corestrict_mkQuotient_iff _).mpr fun W hW ↦ ?_
  obtain ⟨-, W'', hc, -, -⟩ := exists_isCompl_of_isPolarizable hpol
    ⟨W.map b.equivFun.symm.toLinearMap,
      (hs.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_piece hℚ b W).mp hW⟩
  refine ⟨W''.WQ.map b.equivFun.toLinearMap, ?_, ?_⟩
  · have := (Submodule.orderIsoMapComap b.equivFun).isCompl_iff.mp hc
    simpa [Submodule.orderIsoMapComap_apply, ← Submodule.map_comp] using this
  · rw [hs.stabilizerHopfIdeal_le_mumfordTateHopfIdeal_iff_eq_iSup_inf_piece hℚ b,
      ← Submodule.map_comp]
    simpa using W''.hodge_spanning

end TauCeti.Hodge.HodgeStructureOn
