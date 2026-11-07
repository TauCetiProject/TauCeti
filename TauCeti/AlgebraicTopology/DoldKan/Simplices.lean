/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import TauCeti.Algebra.Homology.Embedding.TruncLE
public import TauCeti.AlgebraicTopology.DoldKan.Normalized
public import TauCeti.AlgebraicTopology.DoldKan.SimplexChainMap.Basic
import Mathlib.CategoryTheory.Adjunction.Whiskering
import TauCeti.AlgebraicTopology.SimplicialSet.Cochains.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex
import TauCeti.Data.Finset.Sort

/-!
# The simplices of the Dold–Kan construction

Let `L` be a chain complex in an abelian category `C` with coproducts, and `R` an object of `C`.
Maps `R ⟶ (Γ L) _⦋n⦌` into the `n`-simplices of the Dold–Kan simplicial object `Γ L` are the chain
maps from the simplicial chains `Δ[n].chainComplex R` of the standard simplex to `L` that vanish
on degeneracies, that is, the chain maps out of the normalized chains of `Δ[n]` with coefficients
in `R`. This follows from the Yoneda lemma, the adjunction between `[n] ↦ ∐_{X _⦋n⦌} R` and
`Hom(R, -)`, the Dold–Kan equivalence and the description of the normalized Moore complex as a
retract of the alternating face map complex.

For modules over a ring `R`, in the universe of `R`, and `L = τ_{≥ 0} K` the good truncation of a
cochain complex `K`, take `R` itself as coefficient object. A chain map out of the simplicial
chains of `Δ[n]` is then a family of elements of `K` indexed by the simplices of `Δ[n]`, and
vanishing on degeneracies means vanishing on the simplices that are not injective. The injective
simplices are the increasing enumerations of the nonempty sets `J` of vertices, so these chain
maps are the families `K.SimplexChainMap n`. Hence the simplicial set `K.simplexChainMaps` of
chain maps from the normalized chains of the standard simplices to `τ_{≥ 0} K` is the underlying
simplicial set of `Γ (τ_{≥ 0} K)`: it is the normalized-chain description of the Dold–Kan
construction on the good truncation.

## Main definitions

* `CategoryTheory.Abelian.DoldKan.homΓObjEquiv`: maps `R ⟶ (Γ L) _⦋n⦌` are the chain maps
  `Δ[n].chainComplex R ⟶ L` vanishing on degeneracies.
* `CochainComplex.SimplexChainMap.chainComplexHomEquiv`: the families `K.SimplexChainMap n` are
  the chain maps from the simplicial chains of `Δ[n]` to `τ_{≥ 0} K` vanishing on degeneracies.
* `CochainComplex.simplexChainMapsIso`: the simplicial set `K.simplexChainMaps` is isomorphic to
  the underlying simplicial set of `Γ (τ_{≥ 0} K)`.

## References

* J. Lurie, *Higher Algebra*, Section 1.2.3 and Remark 1.3.1.12.
* P. Goerss and J. Jardine, *Simplicial homotopy theory*, Section III.2.
-/

public section

open CategoryTheory Limits Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan

namespace CategoryTheory.Abelian.DoldKan

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{v} C]

/-- Maps `R ⟶ (Γ L) _⦋n⦌` into the `n`-simplices of the Dold–Kan construction are the chain maps
from the simplicial chains of `Δ[n]` with coefficients in `R` to `L` that vanish on
degeneracies, that is, the chain maps from the normalized chains of `Δ[n]` to `L`. -/
noncomputable def homΓObjEquiv (R : C) (L : ChainComplex C ℕ) (n : ℕ) :
    (R ⟶ (Idempotents.DoldKan.Γ.obj L) _⦋n⦌) ≃
      {f : Δ[n].chainComplex R ⟶ L // ∀ m, DegeneraciesVanish
        (X := ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj Δ[n]) (f.f m)} :=
  SSet.yonedaEquiv.symm.trans <|
    (((sigmaConstAdj R).whiskerRight SimplexCategoryᵒᵖ).homEquiv _ _).symm.trans <|
      (equivalence.toAdjunction.homEquiv _ _).symm.trans <|
        normalizedMooreComplexHomEquiv _ _

/-- `CategoryTheory.Abelian.DoldKan.homΓObjEquiv` is natural: restricting a simplex of `Γ L`
along `θ : ⦋m⦌ ⟶ ⦋n⦌` corresponds to precomposing its chain map with the chain map induced by
`Δ[m] ⟶ Δ[n]`. -/
lemma homΓObjEquiv_naturality (R : C) (L : ChainComplex C ℕ) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (x : R ⟶ (Idempotents.DoldKan.Γ.obj L) _⦋n⦌) :
    (homΓObjEquiv R L m (x ≫ (Idempotents.DoldKan.Γ.obj L).map θ.op)).1 =
      SSet.chainComplexMap (SSet.stdSimplex.map θ) R ≫ (homΓObjEquiv R L n x).1 := by
  have h : (SSet.yonedaEquiv (X := Idempotents.DoldKan.Γ.obj L ⋙ coyoneda.obj (op R))).symm
      (x ≫ (Idempotents.DoldKan.Γ.obj L).map θ.op) =
        SSet.stdSimplex.map θ ≫ SSet.yonedaEquiv.symm x :=
    (SSet.yonedaEquiv_symm_naturality_left
      (X := Idempotents.DoldKan.Γ.obj L ⋙ coyoneda.obj (op R)) θ x).symm
  -- The Dold–Kan equivalence has `normalizedMooreComplex C` as its functor only up to unfolding,
  -- so the naturality of each step is applied under `congrArg` rather than by rewriting.
  refine (congrArg (fun y ↦ (normalizedMooreComplexHomEquiv _ L
    ((equivalence.toAdjunction.homEquiv _ L).symm
      ((((sigmaConstAdj R).whiskerRight SimplexCategoryᵒᵖ).homEquiv _ _).symm y))).1) h).trans ?_
  refine (congrArg (fun y ↦ (normalizedMooreComplexHomEquiv _ L
    ((equivalence.toAdjunction.homEquiv _ L).symm y)).1)
      (Adjunction.homEquiv_naturality_left_symm _ _ _)).trans ?_
  refine (congrArg (fun y ↦ (normalizedMooreComplexHomEquiv _ L y).1)
      (Adjunction.homEquiv_naturality_left_symm _ _ _)).trans ?_
  exact normalizedMooreComplexHomEquiv_naturality _ _

end CategoryTheory.Abelian.DoldKan

namespace CochainComplex

open ComplexShape HomologicalComplex Finset

universe u

variable {R : Type u} [Ring R] {K : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℕ}

/-! ### Chain maps out of the simplicial chains of a standard simplex -/

/-- The value of a chain map from the simplicial chains of `Δ[n]` to `τ_{≥ 0} K` on the
`m`-simplex `α`, as an element of `K` in degree `-m`. -/
private noncomputable def coeff
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat) (m : ℕ)
    (α : Δ[n] _⦋m⦌) : K.X (-(m : ℤ)) :=
  (Δ[n].ιChainComplex α ≫ f.f m ≫ K.truncLE'ToX m).hom (1 : R)

private lemma coeff_injective
    {f f' : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat}
    (h : ∀ m α, coeff f m α = coeff f' m α) : f = f' := by
  ext m : 1
  rw [← cancel_mono (K.truncLE'ToX m)]
  exact (TauCeti.cochainValuesEquiv R _ Δ[n] m).injective <|
    funext fun α ↦ by simpa [coeff] using h m α

private lemma d_coeff (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat)
    (m : ℕ) (α : Δ[n] _⦋m + 1⦌) :
    (K.d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))).hom (coeff f (m + 1) α) =
      ∑ i : Fin (m + 2), ((i : ℕ) : ℤ).negOnePow • coeff f m (Δ[n].δ i α) := by
  have h := Δ[n].ιChainComplex α ≫= f.comm (m + 1) m =≫ K.truncLE'ToX m
  rw [Category.assoc, ← K.truncLE'ToX_d_succ, Category.assoc, SSet.ιChainComplex_d_assoc] at h
  simpa [coeff, Preadditive.sum_comp, Int.negOnePow_def, Units.smul_def] using
    congrArg (fun g ↦ g.hom (1 : R)) h

private lemma coeff_zero_d
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat)
    (α : Δ[n] _⦋0⦌) (j : ℤ) : (K.d (-((0 : ℕ) : ℤ)) j).hom (coeff f 0 α) = 0 := by
  have h := Δ[n].ιChainComplex α ≫= f.f 0 ≫= K.truncLE'ToX_zero_d j
  simpa [coeff] using congrArg (fun g ↦ g.hom (1 : R)) h

/-- A chain map vanishing on degeneracies vanishes on every simplex that is not injective. -/
private lemma coeff_eq_zero
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat)
    (hf : ∀ m, DegeneraciesVanish (X := ((SimplicialObject.whiskering _ _).obj
      (sigmaConst.obj (ModuleCat.of R R))).obj Δ[n]) (f.f m))
    {m : ℕ} (α : Δ[n] _⦋m⦌) (hα : #(univ.image α) ≠ m + 1) : coeff f m α = 0 := by
  obtain _ | m := m
  · exact absurd (by simp) hα
  · have hθ : ¬ Function.Injective (SSet.stdSimplex.objEquiv α).toOrderHom := fun hinj ↦
      hα ((card_image_of_injective _ hinj).trans (by simp))
    obtain ⟨i, θ, hθ⟩ := SimplexCategory.eq_σ_comp_of_not_injective _ hθ
    obtain rfl : α = Δ[n].σ i (SSet.stdSimplex.objEquiv.symm θ) := by
      rw [SSet.stdSimplex.σ_objEquiv_symm_apply, ← hθ, Equiv.symm_apply_apply]
    have h : Δ[n].ιChainComplex (R := ModuleCat.of R R) (SSet.stdSimplex.objEquiv.symm θ) ≫
        (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj (ModuleCat.of R R))).obj
          Δ[n]).σ i = Δ[n].ιChainComplex (Δ[n].σ i (SSet.stdSimplex.objEquiv.symm θ)) :=
      SSet.ιChainComplex_map _ _
    have h' := h =≫ (f.f (m + 1) ≫ K.truncLE'ToX (m + 1))
    rw [Category.assoc, (hf (m + 1)).σ_comp_assoc, zero_comp, comp_zero] at h'
    simpa [coeff] using (congrArg (fun g ↦ g.hom (1 : R)) h').symm

namespace SimplexChainMap

/-! ### From simplex chain maps to chain maps -/

/-- The value of a simplex chain map on an `m`-simplex `α` of `Δ[n]`: its value on the image of
`α` when `α` is injective, and zero otherwise. -/
private noncomputable def simplexVal (g : K.SimplexChainMap n) {m : ℕ} (α : Δ[n] _⦋m⦌) :
    K.X (-(m : ℤ)) :=
  (g.map (SSet.stdSimplex.asOrderHom α)).val univ (-(m : ℤ))

private lemma simplexVal_δ (g : K.SimplexChainMap n) {m : ℕ} (α : Δ[n] _⦋m + 1⦌)
    (i : Fin (m + 2)) :
    g.simplexVal (Δ[n].δ i α) =
      (g.map (SSet.stdSimplex.asOrderHom α)).val (univ.erase i) (-(m : ℤ)) := by
  -- The vertices of the `i`-th face of `α` are those of `α` composed with `i.succAbove`.
  have hcomp : SSet.stdSimplex.asOrderHom (Δ[n].δ i α) =
      (SSet.stdSimplex.asOrderHom α).comp (Fin.succAboveOrderEmb i).toOrderHom := rfl
  have himage : univ.image (Fin.succAboveOrderEmb i).toOrderHom = univ.erase i := by
    ext
    simp
  rw [simplexVal, hcomp, ← map_map, map_val, himage, ite_eq_left (by simp)]

private lemma simplexVal_σ (g : K.SimplexChainMap n) {m : ℕ} (β : Δ[n] _⦋m⦌) (i : Fin (m + 1)) :
    g.simplexVal (Δ[n].σ i β) = 0 := by
  rw [simplexVal, map_val, ite_eq_right]
  intro h
  -- The degeneracy `σ i` repeats the vertex `i` of `β`.
  have := card_image_iff.1 h (by simp) (by simp)
    (show (Δ[n].σ i β) i.castSucc = (Δ[n].σ i β) i.succ by simp [SSet.stdSimplex.σ_apply])
  exact (Fin.castSucc_lt_succ (i := i)).ne this

private lemma d_simplexVal (g : K.SimplexChainMap n) {m : ℕ} (α : Δ[n] _⦋m + 1⦌) :
    (K.d (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ))).hom (g.simplexVal α) =
      ∑ i : Fin (m + 2), ((i : ℕ) : ℤ).negOnePow • g.simplexVal (Δ[n].δ i α) := by
  rw [simplexVal, d_val_of_eq _ _ (by omega)]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [simplexVal_δ, filter_gt_eq_Iio, Fin.card_Iio]

/-- The map from the `m`-chains of `Δ[n]` to `K` in degree `-m` sending the generator of the
`m`-simplex `α` to `g.simplexVal α`. -/
private noncomputable def toX (g : K.SimplexChainMap n) (m : ℕ) :
    (Δ[n].chainComplex (ModuleCat.of R R)).X m ⟶ K.X (-(m : ℤ)) :=
  (TauCeti.cochainValuesEquiv R (K.X (-(m : ℤ))) Δ[n] m).symm g.simplexVal

private lemma ι_toX_apply (g : K.SimplexChainMap n) {m : ℕ} (α : Δ[n] _⦋m⦌) :
    (Δ[n].ιChainComplex α ≫ g.toX m).hom (1 : R) = g.simplexVal α := by
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, toX, TauCeti.cochainValuesEquiv_symm_apply,
    one_smul]

private lemma ι_toX_comp_apply (g : K.SimplexChainMap n) {m : ℕ} (α : Δ[n] _⦋m⦌) {M : ModuleCat R}
    (φ : K.X (-(m : ℤ)) ⟶ M) :
    (Δ[n].ιChainComplex α ≫ g.toX m ≫ φ).hom (1 : R) = φ.hom (g.simplexVal α) := by
  rw [← Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply, ι_toX_apply]

/-- The chain map to the restriction of `K` sending the generator of the `m`-simplex `α` to
`g.simplexVal α`. -/
private noncomputable def toRestriction (g : K.SimplexChainMap n) :
    Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.restriction embeddingDownNat where
  f m := g.toX m ≫ (K.restrictionXIso embeddingDownNat (embeddingDownNat_f m)).inv
  comm' := by
    rintro _ m rfl
    rw [K.restriction_d_eq embeddingDownNat (embeddingDownNat_f (m + 1)) (embeddingDownNat_f m),
      Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    refine SSet.chainComplex_hom_ext fun α ↦ ?_
    rw [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp]
    ext
    refine (g.ι_toX_comp_apply α _).trans ((g.d_simplexVal α).trans ?_)
    simp only [ModuleCat.hom_sum, LinearMap.coe_sum, Finset.sum_apply, Linear.smul_comp,
      ModuleCat.hom_smul, LinearMap.smul_apply, Int.negOnePow_def, Units.smul_def]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [g.ι_toX_apply]
    simp

private lemma toRestriction_comp_d (g : K.SimplexChainMap n) (i : ℕ)
    (hi : embeddingDownNat.BoundaryLE i) (i' : ℤ) (hi' : embeddingDownNat.f i = i') (j' : ℤ) :
    g.toRestriction.f i ≫ (K.restrictionXIso embeddingDownNat hi').hom ≫ K.d i' j' = 0 := by
  obtain rfl := (boundaryLE_embeddingDownNat_iff i).1 hi
  obtain rfl : i' = -((0 : ℕ) : ℤ) := hi'.symm.trans (embeddingDownNat_f 0)
  refine SSet.chainComplex_hom_ext fun α ↦ ?_
  by_cases hj : -((0 : ℕ) : ℤ) + 1 = j'
  · rw [comp_zero, toRestriction, Category.assoc, Iso.inv_hom_id_assoc]
    ext
    refine (g.ι_toX_comp_apply α _).trans ?_
    -- On a vertex, the differential of the value is a sum over faces of the empty set.
    refine (d_val_of_eq _ univ hj).trans (sum_eq_zero fun (j : Fin 1) _ ↦ ?_)
    obtain rfl := Subsingleton.elim j 0
    simp
  · rw [K.shape _ _ hj]
    simp

/-- The chain map from the simplicial chains of `Δ[n]` to `τ_{≥ 0} K` attached to a simplex
chain map. -/
private noncomputable def toChainComplexHom (g : K.SimplexChainMap n) :
    Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat :=
  liftTruncLE' g.toRestriction g.toRestriction_comp_d

private lemma coeff_toChainComplexHom (g : K.SimplexChainMap n) {m : ℕ} (α : Δ[n] _⦋m⦌) :
    coeff g.toChainComplexHom m α = g.simplexVal α := by
  have h := congrArg (fun f ↦ f.f m)
    (liftTruncLE'_truncLE'ToRestriction g.toRestriction g.toRestriction_comp_d)
  simp only [HomologicalComplex.comp_f] at h
  rw [coeff, truncLE'ToX_def, toChainComplexHom, reassoc_of% h]
  rw [toRestriction, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact g.ι_toX_apply α

private lemma degeneraciesVanish_toChainComplexHom (g : K.SimplexChainMap n) (m : ℕ) :
    DegeneraciesVanish (X := ((SimplicialObject.whiskering _ _).obj
      (sigmaConst.obj (ModuleCat.of R R))).obj Δ[n]) (g.toChainComplexHom.f m) := by
  obtain _ | m := m
  · simp
  · rw [degeneraciesVanish_succ_iff]
    intro i
    rw [← cancel_mono ((K.truncLE'ToRestriction embeddingDownNat).f (m + 1)), Category.assoc,
      ← HomologicalComplex.comp_f, toChainComplexHom, liftTruncLE'_truncLE'ToRestriction,
      zero_comp]
    refine SSet.chainComplex_hom_ext fun β ↦ ?_
    have h : Δ[n].ιChainComplex (R := ModuleCat.of R R) β ≫
        (((SimplicialObject.whiskering _ _).obj (sigmaConst.obj (ModuleCat.of R R))).obj
          Δ[n]).σ i = Δ[n].ιChainComplex (Δ[n].σ i β) :=
      SSet.ιChainComplex_map _ _
    rw [reassoc_of% h, comp_zero]
    ext
    refine (g.ι_toX_comp_apply _ _).trans ?_
    rw [simplexVal_σ, map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

/-! ### From chain maps to simplex chain maps -/

/-- The family of values of a chain map on the increasing enumerations of the nonempty sets of
vertices. -/
private noncomputable def ofChainComplexHomVal
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat)
    (J : Finset (Fin (n + 1))) (d : ℤ) : K.X d :=
  if h : d + #J = 1 ∧ J.Nonempty then
    (K.XIsoOfEq (show -((#J - 1 : ℕ) : ℤ) = d by have := h.2.card_pos; omega)).hom
      (coeff f (#J - 1) (SSet.stdSimplex.objMk (m := op ⦋#J - 1⦌)
        (J.orderEmbOfFin (k := #J - 1 + 1) (by have := h.2.card_pos; omega)).toOrderHom))
  else 0

private lemma ofChainComplexHomVal_of_card
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat)
    {J : Finset (Fin (n + 1))} {m : ℕ} (hJ : #J = m + 1) :
    ofChainComplexHomVal f J (-(m : ℤ)) =
      coeff f m (SSet.stdSimplex.objMk (m := op ⦋m⦌) (J.orderEmbOfFin hJ).toOrderHom) := by
  obtain rfl : m = #J - 1 := by omega
  rw [ofChainComplexHomVal, dite_eq_left ⟨by omega, card_pos.1 (by omega)⟩, XIsoOfEq_rfl,
    Iso.refl_hom, ModuleCat.id_apply]

private lemma ofChainComplexHomVal_eq_zero
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat)
    {J : Finset (Fin (n + 1))} {d : ℤ} (h : ¬ (d + #J = 1 ∧ J.Nonempty)) :
    ofChainComplexHomVal f J d = 0 :=
  dite_eq_right h

private lemma d_ofChainComplexHomVal
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat)
    (J : Finset (Fin (n + 1))) (d : ℤ) :
    (K.d d (d + 1)).hom (ofChainComplexHomVal f J d) =
      ∑ j ∈ J, (#{s ∈ J | s < j} : ℤ).negOnePow • ofChainComplexHomVal f (J.erase j) (d + 1) := by
  by_cases hd : d + #J = 1
  · obtain hJ | ⟨k, hk⟩ : #J = 0 ∨ ∃ k, #J = k + 1 := by
      cases #J <;> simp
    · simp [card_eq_zero.1 hJ, ofChainComplexHomVal_eq_zero]
    · obtain _ | m := k
      -- A vertex: its value is a cycle, and its faces are empty.
      · obtain rfl : d = -((0 : ℕ) : ℤ) := by omega
        rw [ofChainComplexHomVal_of_card f hk, coeff_zero_d]
        refine (sum_eq_zero fun j hj ↦ ?_).symm
        rw [ofChainComplexHomVal_eq_zero f fun h ↦ ?_, smul_zero]
        have := card_erase_of_mem hj
        have := h.2.card_pos
        omega
      -- A set of `m + 2` vertices: reindex its faces by the positions of the removed vertex.
      · obtain rfl : d = -((m + 1 : ℕ) : ℤ) := by omega
        rw [show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by omega, ofChainComplexHomVal_of_card f hk,
          d_coeff]
        refine sum_nbij (fun i ↦ J.orderEmbOfFin hk i) (fun i _ ↦ J.orderEmbOfFin_mem hk i)
          (fun i _ j _ h ↦ (J.orderEmbOfFin hk).injective h) (fun j hj ↦ ?_) fun i _ ↦ ?_
        · obtain ⟨i, rfl⟩ : j ∈ Set.range (J.orderEmbOfFin hk) := by
            rwa [range_orderEmbOfFin]
          exact ⟨i, mem_coe.2 (mem_univ i), rfl⟩
        · rw [card_filter_lt_orderEmbOfFin, SSet.stdSimplex.δ_objMk_orderEmbOfFin,
            ofChainComplexHomVal_of_card]
  · rw [ofChainComplexHomVal_eq_zero f fun h ↦ hd h.1, map_zero]
    refine (sum_eq_zero fun j hj ↦ ?_).symm
    rw [ofChainComplexHomVal_eq_zero f fun h ↦ hd ?_, smul_zero]
    have := card_erase_of_mem hj
    have := card_pos.2 ⟨j, hj⟩
    omega

/-- The simplex chain map attached to a chain map from the simplicial chains of `Δ[n]` to
`τ_{≥ 0} K`. -/
private noncomputable def ofChainComplexHom
    (f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat) :
    K.SimplexChainMap n where
  val := ofChainComplexHomVal f
  val_eq_zero_of_ne _ _ h := ofChainComplexHomVal_eq_zero f fun h' ↦ h h'.1
  val_empty := ofChainComplexHomVal_eq_zero f (by simp)
  d_val := d_ofChainComplexHomVal f

/-! ### The comparison -/

/-- The simplex chain maps `K.SimplexChainMap n` are the chain maps from the simplicial chains of
`Δ[n]` to the good truncation `τ_{≥ 0} K` that vanish on degeneracies, that is, the chain maps
from the normalized chains of `Δ[n]` to `τ_{≥ 0} K`. The generator of an injective simplex is sent
to the value of the simplex chain map on its set of vertices, and degenerate simplices to zero
(`CochainComplex.SimplexChainMap.ιChainComplex_chainComplexHomEquiv_f`). -/
noncomputable def chainComplexHomEquiv :
    K.SimplexChainMap n ≃
      {f : Δ[n].chainComplex (ModuleCat.of R R) ⟶ K.truncLE' embeddingDownNat // ∀ m,
        DegeneraciesVanish (X := ((SimplicialObject.whiskering _ _).obj
          (sigmaConst.obj (ModuleCat.of R R))).obj Δ[n]) (f.f m)} where
  toFun g := ⟨g.toChainComplexHom, g.degeneraciesVanish_toChainComplexHom⟩
  invFun f := ofChainComplexHom f.1
  left_inv g := by
    ext J d
    by_cases h : d + #J = 1 ∧ J.Nonempty
    · obtain ⟨m, hm⟩ : ∃ m, #J = m + 1 := ⟨#J - 1, by have := h.2.card_pos; omega⟩
      obtain rfl : d = -(m : ℤ) := by omega
      have himage : univ.image ⇑(SSet.stdSimplex.asOrderHom
          (SSet.stdSimplex.objMk (m := op ⦋m⦌) (J.orderEmbOfFin hm).toOrderHom)) = J :=
        image_orderEmbOfFin_univ J hm
      refine (ofChainComplexHomVal_of_card _ hm).trans ?_
      rw [coeff_toChainComplexHom, simplexVal, map_val, himage, ite_eq_left (hm.trans (by simp))]
    · refine (ofChainComplexHomVal_eq_zero _ h).trans ?_
      by_cases hd : d + #J = 1
      · rw [not_nonempty_iff_eq_empty.1 fun hJ ↦ h ⟨hd, hJ⟩, val_empty']
      · rw [g.val_eq_zero_of_ne _ _ hd]
  right_inv f := by
    refine Subtype.ext (coeff_injective fun m α ↦ ?_)
    rw [coeff_toChainComplexHom, simplexVal, map_val, SSet.stdSimplex.coe_asOrderHom]
    by_cases hα : #(univ.image α) = m + 1
    · rw [ite_eq_left (hα.trans (by simp))]
      exact (ofChainComplexHomVal_of_card f.1 hα).trans
        (congrArg _ (SSet.stdSimplex.objMk_orderEmbOfFin_image α hα))
    · rw [ite_eq_right (fun h ↦ hα (h.trans (by simp))), coeff_eq_zero f.1 f.2 α hα]

/-- The chain map attached to a simplex chain map `g` sends the generator of an `m`-simplex `α`
of `Δ[n]` to the value of `g` pulled back along `α` on all of `Fin (m + 1)`: the value of `g` on
the vertices of `α` if `α` is injective, and zero otherwise. -/
lemma ιChainComplex_chainComplexHomEquiv_f (g : K.SimplexChainMap n) {m : ℕ}
    (α : Δ[n] _⦋m⦌) :
    Δ[n].ιChainComplex α ≫ (chainComplexHomEquiv g).1.f m ≫ K.truncLE'ToX m =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _
        ((g.map (SSet.stdSimplex.asOrderHom α)).val univ (-(m : ℤ)))) := by
  ext
  exact (coeff_toChainComplexHom g α).trans (LinearMap.toSpanSingleton_apply_one R _ _).symm

/-- `CochainComplex.SimplexChainMap.chainComplexHomEquiv` is natural: pulling a simplex chain map
back along `θ : ⦋m⦌ ⟶ ⦋n⦌` corresponds to precomposing its chain map with the chain map induced
by `Δ[m] ⟶ Δ[n]`. -/
lemma chainComplexHomEquiv_map (g : K.SimplexChainMap n) {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (chainComplexHomEquiv (g.map θ.toOrderHom)).1 =
      SSet.chainComplexMap (SSet.stdSimplex.map θ) _ ≫ (chainComplexHomEquiv g).1 :=
  coeff_injective fun j α ↦ by
    have h : coeff (SSet.chainComplexMap (SSet.stdSimplex.map θ) _ ≫ g.toChainComplexHom) j α =
        coeff g.toChainComplexHom j ((SSet.stdSimplex.map θ).app _ α) := by
      simp [coeff]
    refine (coeff_toChainComplexHom _ α).trans (Eq.trans ?_ h.symm)
    rw [coeff_toChainComplexHom, simplexVal, simplexVal, map_map]
    -- The vertices of the image of `α` under `Δ[m] ⟶ Δ[n]` are the images under `θ`.
    rfl

end SimplexChainMap

/-! ### The simplicial set of simplex chain maps -/

variable (K) in
/-- The `n`-simplices of the Dold–Kan construction `Γ (τ_{≥ 0} K)` on the good truncation of `K`
are the simplex chain maps `K.SimplexChainMap n`. -/
noncomputable def simplexChainMapEquiv (n : ℕ) :
    K.SimplexChainMap n ≃ (Idempotents.DoldKan.Γ.obj (K.truncLE' embeddingDownNat)) _⦋n⦌ :=
  SimplexChainMap.chainComplexHomEquiv.trans <|
    (CategoryTheory.Abelian.DoldKan.homΓObjEquiv _ _ n).symm.trans <|
      ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ _).toEquiv

/-- The simplex of `Γ (τ_{≥ 0} K)` attached to a simplex chain map is the image of `1` under the
map `R ⟶ Γ (τ_{≥ 0} K) _⦋n⦌` corresponding to its chain map. -/
lemma simplexChainMapEquiv_apply (g : K.SimplexChainMap n) :
    K.simplexChainMapEquiv n g =
      ((CategoryTheory.Abelian.DoldKan.homΓObjEquiv _ _ n).symm
        (SimplexChainMap.chainComplexHomEquiv g)).hom (1 : R) :=
  (rfl)

/-- `CochainComplex.simplexChainMapEquiv` is compatible with the simplicial operators. -/
lemma simplexChainMapEquiv_map (g : K.SimplexChainMap n) {m : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    K.simplexChainMapEquiv m (g.map θ.toOrderHom) =
      ((Idempotents.DoldKan.Γ.obj (K.truncLE' embeddingDownNat)).map θ.op).hom
        (K.simplexChainMapEquiv n g) := by
  have h : (CategoryTheory.Abelian.DoldKan.homΓObjEquiv _ _ m).symm
      (SimplexChainMap.chainComplexHomEquiv (g.map θ.toOrderHom)) =
      (CategoryTheory.Abelian.DoldKan.homΓObjEquiv _ _ n).symm
        (SimplexChainMap.chainComplexHomEquiv g) ≫
          (Idempotents.DoldKan.Γ.obj (K.truncLE' embeddingDownNat)).map θ.op := by
    rw [Equiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [CategoryTheory.Abelian.DoldKan.homΓObjEquiv_naturality, Equiv.apply_symm_apply]
    exact SimplexChainMap.chainComplexHomEquiv_map g θ
  rw [simplexChainMapEquiv_apply, simplexChainMapEquiv_apply, h, ModuleCat.hom_comp,
    LinearMap.comp_apply]

variable (K) in
/-- **The normalized-chain description of the Dold–Kan construction.** The simplicial set
`K.simplexChainMaps` of chain maps from the normalized chains of the standard simplices to the
good truncation `τ_{≥ 0} K` is isomorphic to the underlying simplicial set of `Γ (τ_{≥ 0} K)`. -/
noncomputable def simplexChainMapsIso :
    K.simplexChainMaps ≅
      Idempotents.DoldKan.Γ.obj (K.truncLE' embeddingDownNat) ⋙ forget (ModuleCat R) :=
  NatIso.ofComponents (fun Δ ↦ (K.simplexChainMapEquiv Δ.unop.len).toIso) fun {Δ Δ'} f ↦ by
    ext g
    exact K.simplexChainMapEquiv_map g f.unop

/-- The isomorphism `CochainComplex.simplexChainMapsIso` sends an `n`-simplex to its image under
`CochainComplex.simplexChainMapEquiv`. -/
@[simp]
lemma simplexChainMapsIso_hom_app_apply (Δ : SimplexCategoryᵒᵖ)
    (g : K.simplexChainMaps.obj Δ) :
    ConcreteCategory.hom (Y := ToType ((Idempotents.DoldKan.Γ.obj
      (K.truncLE' embeddingDownNat)).obj Δ)) (K.simplexChainMapsIso.hom.app Δ) g =
        K.simplexChainMapEquiv Δ.unop.len g :=
  (rfl)

/-- The inverse of `CochainComplex.simplexChainMapsIso` is the inverse of
`CochainComplex.simplexChainMapEquiv`. -/
@[simp]
lemma simplexChainMapsIso_inv_app_apply (Δ : SimplexCategoryᵒᵖ)
    (x : ToType ((Idempotents.DoldKan.Γ.obj (K.truncLE' embeddingDownNat)).obj Δ)) :
    ConcreteCategory.hom (X := ToType ((Idempotents.DoldKan.Γ.obj
      (K.truncLE' embeddingDownNat)).obj Δ)) (K.simplexChainMapsIso.inv.app Δ) x =
        (K.simplexChainMapEquiv Δ.unop.len).symm x :=
  (rfl)

end CochainComplex
