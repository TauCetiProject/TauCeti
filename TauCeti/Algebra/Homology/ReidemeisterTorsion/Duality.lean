/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Dual
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic
import TauCeti.LinearAlgebra.Alternating.Append
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.LinearAlgebra.Dual.Basis

/-!
# The torsion of the dual of a based two-periodic complex

Let `C` be a two-periodic complex of vector spaces over a field `F`, with ordered bases `c 0` of
the even space and `c 1` of the odd space, and let `C^*` be its dual
(`HomologicalComplex.parityDual`), the complex of the dual spaces with the transposed
differentials, based by the dual bases (`HomologicalComplex.parityDualBasis`). Then

`τ(C^*) = τ(C)⁻¹`

(`HomologicalComplex.parityTorsion_parityDual`). Both sides vanish when `C` is not acyclic, since
`C^*` is acyclic exactly when `C` is (`HomologicalComplex.acyclic_parityDual_iff`).

For an acyclic `C`, choose in each degree `j` a basis `bⱼ` of the boundaries `Bⱼ`, the image of
the differential into `Cⱼ`, and lifts `sⱼ` of a basis of the image of the differential out of
`Cⱼ`. In the basis `eⱼ = (bⱼ, sⱼ)` of `Cⱼ`, the differential out of `Cⱼ` kills `bⱼ` and carries
`sⱼ` to the boundaries `bⱼ₊₁` of the other degree. Dually, the transposed differential into
`Cⱼ^*` carries the dual vectors of `bⱼ₊₁` to those of `sⱼ` and kills the dual vectors of `sⱼ₊₁`.
So in `C^*` the boundaries of degree `j` are spanned by the dual vectors of `sⱼ`, which are
lifted by the dual vectors of `bⱼ`: the bracket of `C^*` in degree `j` is the determinant of the
dual basis of `eⱼ` with its two blocks exchanged. Exchanging the blocks costs the same sign in
both degrees, and the determinant of a dual basis with respect to a dual basis is the inverse of
the determinant of the bases themselves (`Module.Basis.det_dualBasis`). Hence each bracket of
`C^*` is, up to that common sign, the inverse of the corresponding bracket of `C`, and the
torsion of `C^*`, the quotient of its odd bracket by its even bracket, is the inverse of the
torsion of `C`. No sign survives, unlike for the dual of a `ℤ`-graded complex, whose brackets are
spread over all degrees.

The torsion of a two-periodic Floer complex over a total quotient ring is read off in each field
component; this formula describes its change when the complex is replaced by its dual, the complex
of the trajectories read in the opposite direction.

## Main declarations

* `HomologicalComplex.parityTorsion_parityDual`: the torsion of the dual complex, based by the dual
  bases, is the inverse of the torsion of `C`.

## References

* J. Milnor, *A duality theorem for Reidemeister torsion*, Ann. of Math. 76 (1962), 137–147.
* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), §2.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

universe u

variable {F : Type u} [Field F]
  {C : HomologicalComplex (ModuleCat.{u} F) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
  (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (h : C.Acyclic) {j k : ZMod 2}

section Adapted

/-- For an acyclic complex and `j + 1 = k`, the basis of `Cⱼ` made of the chosen basis of the
boundaries, the image of the differential from `Cₖ`, followed by the chosen lifts of the chosen
basis of the image of the differential to `Cₖ`. -/
private def adaptedBasis (hjk : j + 1 = k) :
    Basis (Fin (finrank F (LinearMap.range (C.d k j).hom)) ⊕
      Fin (finrank F (LinearMap.range (C.d j k).hom))) F (C.X j) :=
  Basis.ofExactLift (Submodule.injective_subtype _)
    (exact_subtype_rangeRestrict
      ((ComplexShape.up _).prev_eq' (hjk ▸ CharTwo.add_cancel_right j 1))
      ((ComplexShape.up _).next_eq' hjk) (h j))
    (chosenBoundaryBasis C c k j) (chosenBoundaryBasis C c j k) (chosenBoundaryLift C c j k)
    fun l ↦ Subtype.ext (chosenBoundaryLift_spec C c j k l)

private theorem adaptedBasis_inl (hjk : j + 1 = k) (l) :
    adaptedBasis c h hjk (.inl l) = (chosenBoundaryBasis C c k j l : C.X j) := by
  simp [adaptedBasis]

private theorem adaptedBasis_inr (hjk : j + 1 = k) (l) :
    adaptedBasis c h hjk (.inr l) = chosenBoundaryLift C c j k l := by
  simp [adaptedBasis]

/-- The differential out of `Cⱼ` kills the boundaries in the adapted basis. -/
private theorem d_adaptedBasis_inl (hjk : j + 1 = k) (l) :
    (C.d j k).hom (adaptedBasis c h hjk (.inl l)) = 0 := by
  obtain ⟨x, hx⟩ := (chosenBoundaryBasis C c k j l).2
  rw [adaptedBasis_inl, ← hx]
  exact C.d_comp_d_apply k j k x

/-- The differential out of `Cⱼ` carries the lifts in the adapted basis of `Cⱼ` to the boundaries
in the adapted basis of `Cₖ`. -/
private theorem d_adaptedBasis_inr (hjk : j + 1 = k) (hkj : k + 1 = j) (l) :
    (C.d j k).hom (adaptedBasis c h hjk (.inr l)) = adaptedBasis c h hkj (.inl l) := by
  rw [adaptedBasis_inr, adaptedBasis_inl, chosenBoundaryLift_spec]

/-- The transposed differential into `Cₖ^*` carries the dual vectors of the boundaries of `Cⱼ`
to the dual vectors of the lifts in `Cₖ`. -/
private theorem dualMap_d_dualBasis_inl (hjk : j + 1 = k) (hkj : k + 1 = j) (l) :
    (C.d k j).hom.dualMap ((adaptedBasis c h hjk).dualBasis (.inl l)) =
      (adaptedBasis c h hkj).dualBasis (.inr l) := by
  refine (adaptedBasis c h hkj).ext fun i ↦ ?_
  rcases i with m | m
  · simp [d_adaptedBasis_inl c h hkj]
  · simp [d_adaptedBasis_inr c h hkj hjk, Finsupp.single_apply]

/-- The transposed differential into `Cₖ^*` kills the dual vectors of the lifts in `Cⱼ`. -/
private theorem dualMap_d_dualBasis_inr (hjk : j + 1 = k) (hkj : k + 1 = j) (l) :
    (C.d k j).hom.dualMap ((adaptedBasis c h hjk).dualBasis (.inr l)) = 0 := by
  refine (adaptedBasis c h hkj).ext fun i ↦ ?_
  rcases i with m | m
  · simp [d_adaptedBasis_inl c h hkj]
  · simp [d_adaptedBasis_inr c h hkj hjk]

/-- The image of the transposed differential into `Cₖ^*` is spanned by the dual vectors of the
lifts in `Cₖ`. -/
private theorem span_dualBasis_inr (hjk : j + 1 = k) (hkj : k + 1 = j) :
    Submodule.span F (Set.range ((adaptedBasis c h hkj).dualBasis ∘ Sum.inr)) =
      LinearMap.range (C.d k j).hom.dualMap := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨l, rfl⟩
    exact ⟨_, dualMap_d_dualBasis_inl c h hjk hkj l⟩
  · rw [LinearMap.range_eq_map, ← (adaptedBasis c h hjk).dualBasis.span_eq, Submodule.map_span_le]
    rintro _ ⟨l | l, rfl⟩
    · rw [dualMap_d_dualBasis_inl c h hjk hkj]
      exact Submodule.subset_span ⟨l, rfl⟩
    · rw [dualMap_d_dualBasis_inr c h hjk hkj]
      exact zero_mem _

/-- The basis of the image of the transposed differential into `Cₖ^*` made of the dual vectors of
the lifts in `Cₖ`. -/
private def dualBoundaryBasis (hjk : j + 1 = k) (hkj : k + 1 = j) :
    Basis (Fin (finrank F (LinearMap.range (C.d k j).hom))) F
      (LinearMap.range (C.d k j).hom.dualMap) :=
  (Basis.span ((adaptedBasis c h hkj).dualBasis.linearIndependent.comp Sum.inr
    Sum.inr_injective)).map (LinearEquiv.ofEq _ _ (span_dualBasis_inr c h hjk hkj))

private theorem coe_dualBoundaryBasis (hjk : j + 1 = k) (hkj : k + 1 = j) (l) :
    (dualBoundaryBasis c h hjk hkj l : Module.Dual F (C.X k)) =
      (adaptedBasis c h hkj).dualBasis (.inr l) := by
  simp [dualBoundaryBasis]

/-- The dual vectors of the boundaries of `Cⱼ` lift the dual vectors of the lifts in `Cₖ` through
the differential of the dual complex. The equation is stated in `Cₖ^*`, where the subtype
coercion of `dualBoundaryBasis` lands, rather than in the object of the dual complex, so that
`parityDual_d_hom` and `coe_dualBoundaryBasis` rewrite it. -/
private theorem parityDual_d_dualBasis_inl (hjk : j + 1 = k) (hkj : k + 1 = j) (l) :
    @Eq (Module.Dual F (C.X k))
      ((C.parityDual.d j k).hom ((adaptedBasis c h hjk).dualBasis (.inl l)))
      (dualBoundaryBasis c h hjk hkj l) := by
  rw [parityDual_d_hom, coe_dualBoundaryBasis]
  exact dualMap_d_dualBasis_inl c h hjk hkj l

end Adapted

/-- The bracket of the dual complex in degree `j`, for the bases of its boundaries made of the dual
vectors of the chosen lifts of `C` and the lifts made of the dual vectors of the chosen boundary
bases of `C`, times the bracket of `C` in degree `j` for the chosen bases and lifts, is the sign
`(-1) ^ (p * q)`, where `p` and `q` are the ranks of the differentials into and out of `Cⱼ`. -/
private theorem torsionBracket_parityDual_mul_torsionBracket (hjk : j + 1 = k)
    (hkj : k + 1 = j) :
    torsionBracket (parityDualBasis c)
        ((ComplexShape.up _).prev_eq' hkj) ((ComplexShape.up _).next_eq' hjk)
        (C.acyclic_parityDual_iff.2 h j) (dualBoundaryBasis c h hkj hjk)
        (dualBoundaryBasis c h hjk hkj) (fun l ↦ (adaptedBasis c h hjk).dualBasis (.inl l))
        (parityDual_d_dualBasis_inl c h hjk hkj) *
      torsionBracket c ((ComplexShape.up _).prev_eq' hkj) ((ComplexShape.up _).next_eq' hjk) (h j)
        (chosenBoundaryBasis C c k j) (chosenBoundaryBasis C c j k) (chosenBoundaryLift C c j k)
        (chosenBoundaryLift_spec C c j k) =
      (-1) ^ (finrank F (LinearMap.range (C.d k j).hom) *
        finrank F (LinearMap.range (C.d j k).hom)) := by
  set p := finrank F (LinearMap.range (C.d k j).hom)
  set q := finrank F (LinearMap.range (C.d j k).hom)
  have hn : n j = p + q := eq_add_of_exactAt c ((ComplexShape.up _).prev_eq' hkj)
    ((ComplexShape.up _).next_eq' hjk) (h j) (chosenBoundaryBasis C c k j)
    (chosenBoundaryBasis C c j k)
  -- Write `e` for the adapted basis of `Cⱼ`, and `E` for `e` indexed by `Fin (n j)`. The bracket
  -- of `C` is `[E / c j]`.
  set e := adaptedBasis c h hjk with he
  set E := e.reindex (finSumFinEquiv.trans (finCongr hn.symm))
  have hE : Fin.append (fun l ↦ (chosenBoundaryBasis C c k j l : C.X j))
      (chosenBoundaryLift C c j k) ∘ Fin.cast hn = E := by
    rw [Basis.coe_reindex_finSumFinEquiv_trans_finCongr _ hn]
    congr 2 <;> ext l
    exacts [(adaptedBasis_inl c h hjk l).symm, (adaptedBasis_inr c h hjk l).symm]
  -- The bracket of the dual lists the dual basis of `e` with its two blocks exchanged.
  have hD : Fin.append (fun l ↦ (dualBoundaryBasis c h hkj hjk l : Module.Dual F (C.X j)))
      (fun l ↦ e.dualBasis (.inl l)) ∘ Fin.cast (hn.trans (add_comm p q)) =
      (Fin.append (e.dualBasis ∘ Sum.inr) (e.dualBasis ∘ Sum.inl) ∘ Fin.cast (add_comm p q)) ∘
        finCongr hn := by
    ext l
    simp [coe_dualBoundaryBasis, he, Function.comp_def]
  have hED : Fin.append (e.dualBasis ∘ Sum.inl) (e.dualBasis ∘ Sum.inr) ∘ finCongr hn =
      E.dualBasis := by
    rw [Basis.dualBasis_reindex, Basis.coe_reindex_finSumFinEquiv_trans_finCongr _ hn]
    ext l
    simp [finCongr_apply]
  refine (congrArg₂ (· * ·) (torsionBracket_eq_det_append (parityDualBasis c) _ _ _ _ _ _
      (parityDual_d_dualBasis_inl c h hjk hkj) (hn.trans (add_comm p q)))
    (torsionBracket_eq_det_append c _ _ _ _ _ _ _ hn)).trans ?_
  -- Stated for the dual basis of `c j` as a basis of `Cⱼ^*`, rather than of the object of the
  -- dual complex, the determinants can be rewritten.
  have key : (c j).dualBasis.det (Fin.append (fun l ↦ (dualBoundaryBasis c h hkj hjk l :
      Module.Dual F (C.X j))) (fun l ↦ e.dualBasis (.inl l)) ∘
        Fin.cast (hn.trans (add_comm p q))) * (c j).det E = (-1) ^ (p * q) := by
    -- Exchange the two blocks, then compare the dual bases of `E` and `c j`.
    rw [hD, ← Basis.det_reindex, AlternatingMap.map_append_comm, Basis.det_reindex, hED,
      Basis.det_dualBasis, smul_mul_assoc, Basis.det_mul_det, Basis.det_self]
    simp [Units.smul_def]
  rw [hE]
  exact key

/-- **Duality for the torsion of a two-periodic complex.** The torsion of the dual of a based
two-periodic complex, based by the dual bases, is the inverse of the torsion of the complex. Both
sides vanish when the complex is not acyclic. -/
theorem parityTorsion_parityDual :
    C.parityDual.parityTorsion (parityDualBasis c) = (C.parityTorsion c)⁻¹ := by
  by_cases h : C.Acyclic
  swap
  · rw [parityTorsion_of_not_acyclic C c h, inv_zero,
      parityTorsion_of_not_acyclic _ _ (C.acyclic_parityDual_iff.not.2 h)]
  have h₀ : (0 : ZMod 2) + 1 = 1 := zero_add 1
  have h₁ : (1 : ZMod 2) + 1 = 0 := CharTwo.add_self_eq_zero 1
  -- Compute both torsions with the chosen boundary bases and lifts of `C` and their duals.
  rw [parityTorsion_eq h (chosenBoundaryBasis C c 1 0) (chosenBoundaryBasis C c 0 1)
      (chosenBoundaryLift C c 0 1) (chosenBoundaryLift_spec C c 0 1)
      (chosenBoundaryLift C c 1 0) (chosenBoundaryLift_spec C c 1 0),
    parityTorsion_eq (C.acyclic_parityDual_iff.2 h) (dualBoundaryBasis c h h₁ h₀)
      (dualBoundaryBasis c h h₀ h₁) _ (parityDual_d_dualBasis_inl c h h₀ h₁) _
      (parityDual_d_dualBasis_inl c h h₁ h₀)]
  -- Each bracket of the dual is the same sign times the inverse of the bracket of `C`.
  have e₀ := torsionBracket_parityDual_mul_torsionBracket c h h₀ h₁
  have e₁ := torsionBracket_parityDual_mul_torsionBracket c h h₁ h₀
  rw [mul_comm (finrank F _)] at e₁
  rw [eq_div_of_mul_eq (torsionBracket_ne_zero _ _ _ _ _ _ _ _) e₀,
    eq_div_of_mul_eq (torsionBracket_ne_zero _ _ _ _ _ _ _ _) e₁]
  have hs : ((-1 : F) ^ (finrank F (LinearMap.range (C.d 1 0).hom) *
      finrank F (LinearMap.range (C.d 0 1).hom))) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  field_simp

end HomologicalComplex
