/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.Cube.Basic
public import TauCeti.Algebra.Homology.Cube.Dual

/-!
# The totalization of a dual cube is a dual complex

Let `F` be a cube of `R`-modules indexed by a finite linearly ordered type `ι`, and let `C` be its
signed totalization `F.cubeComplex`. The totalization of the dual cube `F.dualCube` is the dual
complex of `C`: the cochain complex `Hom(C, R)` of `R`-linear maps into `R` placed in degree `0`,
which is Mathlib's Hom complex `linearHomComplex R C R[0]`. Its degree-`i` term is identified with
`Hom(C⁻ⁱ, R)` by `CochainComplex.HomComplex.Cochain.toSingleLinearEquiv`, and its differential is
`f ↦ (-1)^(i+1) f ∘ d_C` there.

Complementation reverses the height of a vertex, so both complexes are shifted: for integers `a`
and `b` with `a + b = #ι`, the shift `⟦b⟧` of the totalization of the dual cube is compared with
the dual of the shift `C⟦a⟧`. Normalized complexes are shifts of this kind, with `a` and `b` the
normalization shifts of a complex and of its dual. The vertex `S` of the dual cube is the dual of
the vertex `Sᶜ` of `F`, and the comparison `CategoryTheory.Functor.dualCubeComplexIso` is this
identification on every vertex, multiplied by the sign `Finset.dualCubeSign S a`. The sign is
needed because the cube sign of an edge of the dual cube counts the elements of `S` below the
inserted index, whereas the transposed edge of `F` carries the sign counting the elements of `Sᶜ`
below it; the shifts contribute the signs `(-1)^a` and `(-1)^b` of their differentials.

## Main definitions

* `Finset.dualCubeSign S a`: the vertex sign of the comparison, characterized by
  `Finset.dualCubeSign_empty` and `Finset.dualCubeSign_insert`.
* `CategoryTheory.Functor.dualCubeComplexIso F hab`: the isomorphism from the shifted
  totalization of the dual cube to the dual complex of the shifted totalization of `F`, given
  on vertices by `Functor.dualCubeComplexIso_hom_f_apply` and
  `Functor.dualCubeComplexIso_inv_f_apply`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.
-/

public section

noncomputable section

open CategoryTheory Limits Finset CochainComplex HomComplex

universe w u

variable {ι : Type w} [Fintype ι] [LinearOrder ι]

namespace Finset

/-- The sign of the vertex `S` in the comparison of the totalization of a dual cube with the dual
of the totalization of a cube shifted by `a`: `(-1)` to the power
`∑_{x ∈ S} #{y < x} + (#S + 1 choose 2) + a #S`. -/
def dualCubeSign (S : Finset ι) (a : ℤ) : ℤˣ :=
  ((∑ x ∈ S, #{y | y < x} : ℕ) + ((#S + 1).choose 2 : ℕ) + a * #S : ℤ).negOnePow

/-- The empty vertex has sign `1`. -/
@[simp]
theorem dualCubeSign_empty (a : ℤ) : (∅ : Finset ι).dualCubeSign a = 1 := by
  simp [dualCubeSign]

/-- Inserting a new index `c` into a vertex of height `#S` multiplies the sign by `(-1)` to the
power `#S + 1 + a + #{y < c}`. -/
theorem dualCubeSign_insert {S : Finset ι} {c : ι} (hc : c ∉ S) (a : ℤ) :
    (insert c S).dualCubeSign a =
      ((#S : ℤ) + 1 + a + #{y | y < c}).negOnePow * S.dualCubeSign a := by
  rw [dualCubeSign, dualCubeSign, ← Int.negOnePow_add, Int.negOnePow_eq_iff, sum_insert hc,
    card_insert_of_notMem hc, Nat.choose_succ_succ' (#S + 1), Nat.choose_one_right]
  exact ⟨0, by push_cast; ring⟩

end Finset

namespace CategoryTheory.Functor

variable {R : Type u} [CommRing R] (F : Finset ι ⥤ ModuleCat.{u} R)

/-- Two projections onto the same vertex, followed by edge maps to a common vertex, agree. -/
private lemma cubeComplexπ_map_congr {r : ℤ} {V W : {S : Finset ι // (#S : ℤ) = r}}
    (h : V.1 = W.1) {T : Finset ι} (hV : V.1 ⊆ T) (hW : W.1 ⊆ T) :
    F.cubeComplexπ V ≫ F.map (homOfLE hV) = F.cubeComplexπ W ≫ F.map (homOfLE hW) := by
  obtain ⟨V, _⟩ := V
  obtain ⟨W, _⟩ := W
  dsimp only at h
  subst h
  rfl

/-- The cube differential out of a vertex, into the term of any height `r'` with `r + 1 = r'`. -/
private lemma ι_cubeComplex_d' {r r' : ℤ} (h : r + 1 = r') (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexι S ≫ F.cubeComplex.d r r' =
      ∑ c : (S.1ᶜ : Finset ι), ((-1 : ℤ) ^ #{y ∈ S.1 | y < c.1}) •
        F.map (homOfLE (S.1.subset_insert c.1)) ≫
          F.cubeComplexι ⟨insert c.1 S.1, by
            rw [card_insert_of_notMem (mem_compl.1 c.2), Nat.cast_succ, S.2, h]⟩ := by
  subst h
  exact F.ι_cubeComplex_d S

/-- The cube differential into a vertex, out of the term of any height `r` with `r + 1 = r'`. -/
private lemma cubeComplex_d_π' {r r' : ℤ} (h : r + 1 = r') (T : {T : Finset ι // (#T : ℤ) = r'}) :
    F.cubeComplex.d r r' ≫ F.cubeComplexπ T =
      ∑ c : T.1, ((-1 : ℤ) ^ #{y ∈ T.1.erase c.1 | y < c.1}) •
        F.cubeComplexπ (r := r)
          ⟨T.1.erase c.1, by have := card_erase_add_one c.2; have := T.2; omega⟩ ≫
          F.map (homOfLE (T.1.erase_subset c.1)) := by
  subst h
  exact F.cubeComplex_d_π T

/-- The indices below `c` are those of `S` and those of `Sᶜ \ {c}`. -/
private lemma card_filter_lt_eq (S : Finset ι) (c : ι) :
    #{y | y < c} = #{y ∈ S | y < c} + #{y ∈ Sᶜ.erase c | y < c} := by
  rw [filter_erase, erase_eq_of_notMem (by simp), ← card_union_of_disjoint
    (disjoint_filter_filter disjoint_compl_right), ← filter_union, union_compl]

variable {a b : ℤ} (hab : a + b = Fintype.card ι)

include hab in
/-- The complement of a vertex of height `i + b` has height `-i + a`. -/
private lemma card_compl_eq {i : ℤ} {S : Finset ι} (hS : (#S : ℤ) = i + b) :
    (#Sᶜ : ℤ) = -i + a := by
  have := card_compl_add_card S
  omega

/-- The vertex `S` of the comparison: a linear form `φ` on `F(Sᶜ)` goes to the signed cochain
`C⁻ⁱ⁺ᵃ ⟶ F(Sᶜ) ⟶ R`. -/
private def homVertex (i : ℤ) (S : {S : Finset ι // (#S : ℤ) = i + b}) :
    F.dualCube.obj S.1 ⟶ ModuleCat.of R (Cochain (F.cubeComplex⟦a⟧)
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) i) :=
  ModuleCat.ofHom
    { toFun φ := S.1.dualCubeSign a •
        Cochain.toSingleMk (K := F.cubeComplex⟦a⟧) (p := -i)
          (F.cubeComplexπ ⟨S.1ᶜ, card_compl_eq hab S.2⟩ ≫ ModuleCat.ofHom φ) (neg_add_cancel i)
      map_add' φ ψ := by simp
      map_smul' r φ := by
        rw [RingHom.id_apply, show ModuleCat.ofHom (r • φ) = r • ModuleCat.ofHom φ from rfl,
          Linear.comp_smul, Cochain.toSingleMk_smul]
        exact smul_comm _ _ _ }

/-- The vertex `S` of the inverse comparison: a cochain `f : C⁻ⁱ⁺ᵃ ⟶ R` goes to the signed linear
form `F(Sᶜ) ⟶ C⁻ⁱ⁺ᵃ ⟶ R`. -/
private def invVertex (i : ℤ) (S : {S : Finset ι // (#S : ℤ) = i + b}) :
    ModuleCat.of R (Cochain (F.cubeComplex⟦a⟧)
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) i) ⟶ F.dualCube.obj S.1 :=
  ModuleCat.ofHom
    { toFun f := S.1.dualCubeSign a •
        (F.cubeComplexι ⟨S.1ᶜ, card_compl_eq hab S.2⟩ ≫
          Cochain.toSingleEquiv (neg_add_cancel i) f).hom
      map_add' f g := by simp
      map_smul' r f := by
        simp only [RingHom.id_apply, Cochain.toSingleEquiv_smul, Linear.comp_smul,
          ModuleCat.hom_smul]
        exact smul_comm _ _ _ }

private lemma homVertex_apply (i : ℤ) (S : {S : Finset ι // (#S : ℤ) = i + b})
    (φ : F.dualCube.obj S.1) :
    (homVertex F hab i S).hom φ = S.1.dualCubeSign a •
      Cochain.toSingleMk (K := F.cubeComplex⟦a⟧) (p := -i)
        (F.cubeComplexπ ⟨S.1ᶜ, card_compl_eq hab S.2⟩ ≫ ModuleCat.ofHom φ) (neg_add_cancel i) :=
  rfl

private lemma invVertex_apply (i : ℤ) (S : {S : Finset ι // (#S : ℤ) = i + b})
    (f : Cochain (F.cubeComplex⟦a⟧)
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) i) :
    (invVertex F hab i S).hom f = S.1.dualCubeSign a •
      (F.cubeComplexι ⟨S.1ᶜ, card_compl_eq hab S.2⟩ ≫
        Cochain.toSingleEquiv (neg_add_cancel i) f).hom :=
  rfl

/-- The complement bijection between the vertices of height `i + b` and of height `-i + a`. -/
private def complEquiv (i : ℤ) :
    {S : Finset ι // (#S : ℤ) = i + b} ≃ {T : Finset ι // (#T : ℤ) = -i + a} where
  toFun S := ⟨S.1ᶜ, card_compl_eq hab S.2⟩
  invFun T := ⟨T.1ᶜ, by have := card_compl_add_card T.1; have := T.2; omega⟩
  left_inv S := Subtype.ext (compl_compl S.1)
  right_inv T := Subtype.ext (compl_compl T.1)

/-- The comparison in degree `i`. -/
private def dualCubeComplexXIso (i : ℤ) :
    (F.dualCube.cubeComplex⟦b⟧).X i ≅ (linearHomComplex R (F.cubeComplex⟦a⟧)
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).X i where
  hom := F.dualCube.cubeComplexDesc (r := i + b) (homVertex F hab i)
  inv := F.dualCube.cubeComplexLift (r := i + b) (invVertex F hab i)
  hom_inv_id := by
    refine F.dualCube.cubeComplex_hom_ext (r := i + b) fun S ↦
      F.dualCube.cubeComplex_hom_ext' (r := i + b) fun T ↦ ?_
    simp only [Category.assoc, ι_cubeComplexDesc_assoc, cubeComplexLift_π]
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ LinearMap.ext fun x ↦ ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [invVertex_apply, homVertex_apply]
    simp only [Units.smul_def, shiftFunctor_obj_X', Cochain.toSingleEquiv_smul,
      Cochain.toSingleEquiv_toSingleMk, ModuleCat.hom_smul, ModuleCat.hom_comp,
      ConcreteCategory.hom_ofHom, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      zsmul_eq_mul, ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    by_cases h : S = T
    · subst h
      have e₁ := congrArg (fun f ↦ f.hom x) (F.cubeComplexι_π_self ⟨S.1ᶜ, card_compl_eq hab S.2⟩)
      have e₂ := congrArg (fun f ↦ f.hom φ x) (F.dualCube.cubeComplexι_π_self S)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] at e₁ e₂
      rw [e₁, e₂, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
        Units.val_one, Int.cast_one, one_mul]
    · have h' : (⟨T.1ᶜ, card_compl_eq hab T.2⟩ : {U : Finset ι // (#U : ℤ) = -i + a}) ≠
          ⟨S.1ᶜ, card_compl_eq hab S.2⟩ :=
        fun e ↦ h (Subtype.ext (compl_injective (congrArg Subtype.val e).symm))
      have e₁ := congrArg (fun f ↦ f.hom x) (F.cubeComplexι_π_of_ne h')
      have e₂ := congrArg (fun f ↦ f.hom φ x) (F.dualCube.cubeComplexι_π_of_ne h)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at e₁ e₂
      simp [e₁, e₂]
  inv_hom_id := by
    rw [← Category.id_comp (F.dualCube.cubeComplexDesc (r := i + b) _),
      ← F.dualCube.cubeComplex_total,
      Preadditive.sum_comp, Preadditive.comp_sum]
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦
      (Cochain.toSingleEquiv (neg_add_cancel i)).injective ?_)
    simp only [Category.assoc, ι_cubeComplexDesc, cubeComplexLift_π_assoc, ModuleCat.hom_sum,
      LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply, _root_.map_sum,
      ModuleCat.hom_id, LinearMap.id_apply]
    -- Each vertex contributes the projection to `F(Sᶜ)` followed by the inclusion of `F(Sᶜ)`.
    have key (S : {S : Finset ι // (#S : ℤ) = i + b}) :
        Cochain.toSingleEquiv (neg_add_cancel i) ((homVertex F hab i S).hom
          ((invVertex F hab i S).hom z)) =
        F.cubeComplexπ ⟨S.1ᶜ, card_compl_eq hab S.2⟩ ≫
          F.cubeComplexι ⟨S.1ᶜ, card_compl_eq hab S.2⟩ ≫
            Cochain.toSingleEquiv (neg_add_cancel i) z := by
      rw [homVertex_apply, invVertex_apply, ← ModuleCat.hom_smul, ModuleCat.ofHom_hom,
        Linear.comp_units_smul, Units.smul_def, _root_.map_zsmul, Cochain.toSingleEquiv_toSingleMk,
        ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
    simp only [key, ← Category.assoc]
    rw [← Preadditive.sum_comp, Fintype.sum_equiv (complEquiv hab i)
      (fun S ↦ F.cubeComplexπ ⟨S.1ᶜ, card_compl_eq hab S.2⟩ ≫
        F.cubeComplexι ⟨S.1ᶜ, card_compl_eq hab S.2⟩)
      (fun T ↦ F.cubeComplexπ T ≫ F.cubeComplexι T) (fun _ ↦ rfl), F.cubeComplex_total,
      Category.id_comp]

/-- Along an edge `S ⟶ insert c S` of the dual cube, the vertex signs, the shifts and the
cube signs of the edge and of its transpose in `F` match. -/
private lemma dualCubeSign_edge {i : ℤ} {S : Finset ι} (hS : (#S : ℤ) = i + b) {c : ι}
    (hc : c ∉ S) :
    S.dualCubeSign a * (i + 1).negOnePow * a.negOnePow *
        ((#{y ∈ Sᶜ.erase c | y < c} : ℕ) : ℤ).negOnePow =
      b.negOnePow * ((#{y ∈ S | y < c} : ℕ) : ℤ).negOnePow * (insert c S).dualCubeSign a := by
  rw [Finset.dualCubeSign_insert hc]
  simp only [Finset.dualCubeSign, ← Int.negOnePow_add]
  rw [Int.negOnePow_eq_iff, Int.even_iff]
  have := card_filter_lt_eq S c
  omega

private lemma dualCubeComplexXIso_comm (i : ℤ) :
    (dualCubeComplexXIso F hab i).hom ≫ (linearHomComplex R (F.cubeComplex⟦a⟧)
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))).d i (i + 1) =
      (F.dualCube.cubeComplex⟦b⟧).d i (i + 1) ≫ (dualCubeComplexXIso F hab (i + 1)).hom := by
  refine F.dualCube.cubeComplex_hom_ext (r := i + b) fun S ↦ ?_
  simp only [dualCubeComplexXIso, ι_cubeComplexDesc_assoc, shiftFunctor_obj_d', Units.smul_def,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    reassoc_of% (F.dualCube.ι_cubeComplex_d' (show i + b + 1 = i + 1 + b by ring) S),
    Preadditive.sum_comp, Category.assoc, ι_cubeComplexDesc]
  refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦
    (Cochain.toSingleEquiv (neg_add_cancel (i + 1))).injective ?_)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_sum, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, _root_.map_sum, _root_.map_zsmul]
  rw [linearHomComplex_d_hom_apply, homVertex_apply, δ_units_smul,
    Cochain.δ_toSingleMk (h' := neg_add_cancel (i + 1)), shiftFunctor_obj_d',
    Units.smul_def, Units.smul_def, Units.smul_def, _root_.map_zsmul, _root_.map_zsmul,
    Cochain.toSingleEquiv_toSingleMk]
  dsimp only
  have hd := F.cubeComplex_d_π' (r := -(i + 1) + a) (r' := -i + a) (by ring)
    ⟨S.1ᶜ, card_compl_eq hab S.2⟩
  rw [Preadditive.zsmul_comp, reassoc_of% hd]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hc : c.1 ∉ S.1 := mem_compl.1 c.2
  rw [homVertex_apply, Units.smul_def, _root_.map_zsmul, Cochain.toSingleEquiv_toSingleMk,
    smul_smul]
  -- The transposed edge map of `F`, out of `(insert c S)ᶜ = Sᶜ \ {c}`.
  have hm : F.cubeComplexπ (r := -(i + 1) + a) ⟨S.1ᶜ.erase c.1, by
        have := card_erase_add_one c.2; have := card_compl_eq hab S.2; omega⟩ ≫
      F.map (homOfLE (S.1ᶜ.erase_subset c.1)) ≫ ModuleCat.ofHom φ =
      F.cubeComplexπ ⟨(insert c.1 S.1)ᶜ, card_compl_eq hab (i := i + 1) (by
        rw [card_insert_of_notMem hc, Nat.cast_succ, S.2]; ring)⟩ ≫ ModuleCat.ofHom
        ((F.map (homOfLE (compl_subset_compl.2 (S.1.subset_insert c.1)))).hom.dualMap φ) :=
    (reassoc_of% (F.cubeComplexπ_map_congr compl_insert.symm _ _)) (ModuleCat.ofHom φ)
  have hs := congrArg (fun u : ℤˣ ↦ (u : ℤ)) (dualCubeSign_edge (a := a) S.2 hc)
  push_cast [Units.val_mul, Int.coe_negOnePow_natCast] at hs
  dsimp only
  rw [ModuleCat.hom_ofHom, hm, ← mul_assoc, ← mul_assoc, hs]

/-- **The totalization of a dual cube is a dual complex.** For integers `a` and `b` with
`a + b = #ι`, the shift by `b` of the totalization of the dual cube `F.dualCube` is isomorphic to
the dual `Hom(C⟦a⟧, R)` of the shift by `a` of the totalization `C` of `F`. On the vertex `S` of
height `i + b` it sends a linear form on `F(Sᶜ)` to its composite with the projection of `C⁻ⁱ⁺ᵃ`
onto `F(Sᶜ)`, multiplied by `Finset.dualCubeSign S a`
(`CategoryTheory.Functor.dualCubeComplexIso_hom_f_apply`). -/
def dualCubeComplexIso :
    F.dualCube.cubeComplex⟦b⟧ ≅ linearHomComplex R (F.cubeComplex⟦a⟧)
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
  HomologicalComplex.Hom.isoOfComponents (dualCubeComplexXIso F hab) (by
    rintro i _ rfl
    exact dualCubeComplexXIso_comm F hab i)

/-- The comparison sends a linear form `φ` on the vertex `F(Sᶜ)` to the cochain
`C⁻ⁱ⁺ᵃ ⟶ F(Sᶜ) ⟶ R` of degree `i`, multiplied by the sign of `S`. -/
theorem dualCubeComplexIso_hom_f_apply (i : ℤ) (S : {S : Finset ι // (#S : ℤ) = i + b})
    (φ : Module.Dual R (F.obj S.1ᶜ)) :
    ((F.dualCubeComplexIso hab).hom.f i).hom ((F.dualCube.cubeComplexι S).hom φ) =
      S.1.dualCubeSign a • Cochain.toSingleMk (K := F.cubeComplex⟦a⟧) (p := -i)
        (F.cubeComplexπ (r := -i + a) ⟨S.1ᶜ, by
          have := card_compl_add_card S.1; have := S.2; have := hab; omega⟩ ≫
          ModuleCat.ofHom φ) (neg_add_cancel i) :=
  congrArg (fun g ↦ g.hom φ) (F.dualCube.ι_cubeComplexDesc (homVertex F hab i) S)

/-- The inverse comparison sends a cochain `f : C⁻ⁱ⁺ᵃ ⟶ R` of degree `i` to the linear form
`F(Sᶜ) ⟶ C⁻ⁱ⁺ᵃ ⟶ R` on each vertex `S`, multiplied by the sign of `S`. -/
theorem dualCubeComplexIso_inv_f_apply (i : ℤ) (S : {S : Finset ι // (#S : ℤ) = i + b})
    (f : Cochain (F.cubeComplex⟦a⟧)
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) i) :
    (F.dualCube.cubeComplexπ S).hom (((F.dualCubeComplexIso hab).inv.f i).hom f) =
      S.1.dualCubeSign a •
        (F.cubeComplexι (r := -i + a) ⟨S.1ᶜ, by
          have := card_compl_add_card S.1; have := S.2; have := hab; omega⟩ ≫
          Cochain.toSingleEquiv (K := F.cubeComplex⟦a⟧) (p := -i) (neg_add_cancel i) f).hom :=
  congrArg (fun g ↦ g.hom f) (F.dualCube.cubeComplexLift_π (invVertex F hab i) S)

end CategoryTheory.Functor
