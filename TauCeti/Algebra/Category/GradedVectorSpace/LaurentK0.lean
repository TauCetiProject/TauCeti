/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedVectorSpace.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.GradedDimension
public import TauCeti.CategoryTheory.Exact.Graded.FullSubcategory
public import TauCeti.CategoryTheory.GrothendieckGroup.Laurent.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The graded Grothendieck group of finite-dimensional graded vector spaces

Let `k` be a field. A `ℤ`-graded vector space is *finite* when its total space is
finite-dimensional, that is, when every piece is finite-dimensional and only finitely many pieces
are nonzero (`TauCeti.HasFiniteLaurentSupport`). Finite graded vector spaces form a shift-stable,
extension-closed, essentially small full subcategory of `TauCeti.GradedVectorSpace k`, so they
carry a graded exact structure and a graded Grothendieck group `K₀^gr`, a module over
`ℤ[q,q⁻¹]` in which `[V{1}] = q[V]`.

This group is free of rank one on the class of `M = k`, placed in degree `0`. The graded dimension
`gdim V = ∑ⱼ dim_k(Vⱼ) qʲ` is additive on short exact sequences and turns the shift into
multiplication by `q`, so it descends to a `ℤ[q,q⁻¹]`-linear map on `K₀^gr`. Conversely every
class is a Laurent multiple of `[M]`: a nonzero vector in degree `j` spans a copy of `M{j}`, and
splitting it off lowers the total dimension. Hence

```text
K₀^gr ≃ ℤ[q,q⁻¹],    [V] ↦ gdim V,    [M{n}] ↦ qⁿ.
```

Since `[M{n}] = qⁿ[M]`, the shifts of `M` have pairwise distinct classes, although forgetting the
grading sends all of them to the same vector space `k`.

Consequently the specialization of `K₀^gr` at any `q = ε` is still free of rank one on the class of
`M`, with coordinate `gdim V` evaluated at `q = ε`. In particular, at `q = -1` the sign
`[M{1}] = -[M]` produced by a single shift is a genuine change of class.

## Main definitions

* `TauCeti.GradedVectorSpace.finite`: the finite graded vector spaces.
* `TauCeti.GradedVectorSpace.finiteExactStructure`: their graded exact structure, induced from the
  canonical exact structure of the abelian category of graded vector spaces.
* `TauCeti.GradedVectorSpace.unitFinite`: the one-dimensional space `M = k` in degree `0`.
* `TauCeti.GradedVectorSpace.laurentK0Equiv`: the graded dimension
  `K₀^gr ≃ ℤ[q,q⁻¹]` of finite graded vector spaces.
* `TauCeti.GradedVectorSpace.laurentSpecializationBasis`: the basis `[M]` of `K₀^gr` specialized
  at `q = ε`.

## Main results

* `TauCeti.GradedVectorSpace.isExtensionClosed_finite` and
  `TauCeti.GradedVectorSpace.finite_shift`: finite graded vector spaces are closed under
  extensions and stable under the grading shift.
* `TauCeti.GradedVectorSpace.laurentK0Equiv_of`: the graded dimension of the class `[V]` is
  `gdim V`.
* `TauCeti.GradedVectorSpace.of_eq_gradedDimension_smul`: `[V] = gdim V · [M]`.
* `TauCeti.GradedVectorSpace.mk_neg_one_of_shift_unitFinite_ne`: at `q = -1` the classes of `M{1}`
  and `M` differ.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for the graded Grothendieck group
  as a `ℤ[q,q⁻¹]`-module and the normalization `[M{1}] = q[M]`.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  for Grothendieck groups of finite-dimensional vector spaces.
-/

public section

open scoped DirectSum

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe u

variable (k : Type u) [Field k]

namespace GradedVectorSpace

/-! ### Finite graded vector spaces -/

/-- The **finite graded vector spaces**: every piece is finite-dimensional and only finitely many
pieces are nonzero. -/
def finite : ObjectProperty (GradedVectorSpace k) :=
  fun V ↦ HasFiniteLaurentSupport k fun j ↦ (V j : Type u)

variable {k} in
/-- Characterization of `TauCeti.GradedVectorSpace.finite`, for importing modules, to which the
body of the definition is not exposed. -/
@[simp]
theorem finite_iff (V : GradedVectorSpace k) :
    finite k V ↔ HasFiniteLaurentSupport k fun j ↦ (V j : Type u) :=
  Iff.rfl

/-- Finiteness of a graded vector space is invariant under graded isomorphism. -/
instance : (finite k).IsClosedUnderIsomorphisms where
  of_iso e hV := HasFiniteLaurentSupport.of_equiv hV fun j ↦ (Pi.isoApp e j).toLinearEquiv

/-- The zero graded vector space is finite. -/
instance : (finite k).ContainsZero where
  exists_zero := by
    let Z : GradedVectorSpace k := fun _ ↦ ModuleCat.of k PUnit
    refine ⟨Z, (IsZero.iff_id_eq_zero Z).2 (funext fun j ↦ ?_), ?_⟩
    · exact (ModuleCat.isZero_of_subsingleton (Z j)).eq_of_src _ _
    · exact HasFiniteLaurentSupport.of_finset (fun _ ↦ inferInstance) ∅
        fun _ _ ↦ inferInstanceAs (Subsingleton PUnit)

/-- **Finite graded vector spaces are closed under extensions**: a short exact sequence of graded
vector spaces is short exact in every degree. -/
theorem isExtensionClosed_finite :
    (ExactStructure.abelian (GradedVectorSpace k)).IsExtensionClosed (finite k) where
  prop_X₂ {S} hS h₁ h₃ := by
    have hS' (j : ℤ) := ((ExactStructure.abelian_conflation S).1 hS).map_of_exact
      (GradedObject.eval j)
    exact HasFiniteLaurentSupport.of_exact h₁ h₃ (fun j ↦ (S.f j).hom) (fun j ↦ (S.g j).hom)
      fun j ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS' j).exact

/-- Finite graded vector spaces are closed under binary products (direct sums). -/
instance : (finite k).IsClosedUnderBinaryProducts :=
  (isExtensionClosed_finite k).isClosedUnderBinaryProducts

/-- **Finite graded vector spaces are stable under the grading shift**: a graded vector space is
finite exactly when its shift `V{1}`, with `(V{1})ⱼ = V_{j-1}`, is. -/
theorem finite_shift : (finite k).inverseImage (shift k).functor = finite k := by
  ext V
  simp only [ObjectProperty.prop_inverseImage_iff, finite_iff, GradedObject.shiftFunctor_obj_apply,
    shiftEquiv'_functor]
  refine ⟨fun h ↦ (h.reindex_add 1).of_equiv fun j ↦ ?_, fun h ↦ (h.reindex_add (-1)).of_equiv
    fun j ↦ ?_⟩
  all_goals exact (eqToIso (congrArg V (by simp))).toLinearEquiv

/-- A small family of graded vector spaces, indexed by the dimensions of the pieces, containing
every finite graded vector space up to isomorphism. -/
private def model (d : ℤ → ℕ) : GradedVectorSpace k :=
  fun j ↦ ModuleCat.of k (Fin (d j) → k)

/-- Finite graded vector spaces are essentially small: up to isomorphism, each one is a
family of coordinate spaces `Fin (dim Vⱼ) → k`, indexed by the dimensions of its pieces. -/
instance : ObjectProperty.EssentiallySmall.{u} (finite k) where
  exists_small_le' := by
    refine ⟨.ofObj (model k), inferInstance, fun V hV ↦ ?_⟩
    have := hV.finiteDimensional
    refine ⟨_, ⟨fun j ↦ Module.finrank k (V j)⟩, ⟨GradedObject.isoMk _ _ fun j ↦ ?_⟩⟩
    exact (LinearEquiv.ofFinrankEq _ _ (by simp)).toModuleIso

/-- The **graded exact structure of finite graded vector spaces**, induced from the canonical exact
structure of the abelian category of graded vector spaces, with the grading shift `V ↦ V{1}`. -/
noncomputable def finiteExactStructure : GradedExactStructure (finite k).FullSubcategory :=
  (GradedExactStructure.abelian _ (shift k)).fullSubcategory (finite k)
    (by simpa using isExtensionClosed_finite k) (by simpa using finite_shift k)

/-- The graded exact structure of finite graded vector spaces is the one induced on the full
subcategory from the abelian category of graded vector spaces with its grading shift. -/
theorem finiteExactStructure_def :
    finiteExactStructure k =
      (GradedExactStructure.abelian _ (shift k)).fullSubcategory (finite k)
        (by simpa using isExtensionClosed_finite k) (by simpa using finite_shift k) :=
  (rfl)

/-- The conflations of finite graded vector spaces are the short exact sequences. -/
@[simp]
theorem finiteExactStructure_conflation_iff (S : ShortComplex (finite k).FullSubcategory) :
    (finiteExactStructure k).Conflation S ↔ (S.map (finite k).ι).ShortExact := by
  rw [finiteExactStructure, GradedExactStructure.fullSubcategory_conflation_iff,
    GradedExactStructure.abelian_toExactStructure, ExactStructure.abelian_conflation]

/-- The grading shift of finite graded vector spaces is the ambient grading shift. -/
private noncomputable def shiftObjIso (V : (finite k).FullSubcategory) :
    ((finiteExactStructure k).shift.functor.obj V).obj ≅ (shift k).functor.obj V.obj := by
  rw [finiteExactStructure, GradedExactStructure.fullSubcategory_shift]
  refine (GradedExactStructure.fullSubcategoryShiftFunctorCompιIso _ (finite k) ?_).app V ≪≫
    eqToIso ?_
  · simpa using finite_shift k
  · simp

/-- The piece of `V{1}` in degree `j` is the piece of `V` in degree `j - 1`. -/
private noncomputable def shiftObjApplyIso (V : (finite k).FullSubcategory) (j : ℤ) :
    ((finiteExactStructure k).shift.functor.obj V).obj j ≅ V.obj (j - 1) :=
  Pi.isoApp (shiftObjIso k V) j ≪≫ eqToIso (congrArg V.obj (by simp [sub_eq_add_neg]))

/-- A finite-dimensional vector space placed in a single degree `j` is a finite graded vector
space. -/
theorem finite_single (j : ℤ) (Y : ModuleCat.{u} k) [Module.Finite k Y] :
    finite k ((GradedObject.single j).obj Y) := by
  refine (finite_iff _).2 <| HasFiniteLaurentSupport.of_finset (fun i ↦ ?_) {j} fun i hi ↦
    ModuleCat.subsingleton_of_isZero
      (GradedObject.isInitialSingleObjApply j Y i (by simpa using hi)).isZero
  by_cases hi : i = j
  · exact Module.Finite.equiv (R := k)
      (GradedObject.singleObjApplyIsoOfEq j Y i hi).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero
      (GradedObject.isInitialSingleObjApply j Y i hi).isZero
    infer_instance

/-- The one-dimensional space `M = k` in degree `0` is finite. -/
theorem finite_unit : finite k (unit k) :=
  unit_def k ▸ finite_single k 0 (ModuleCat.of k k)

/-- The pieces of the one-dimensional space `M = k` in degree `0` have finite Laurent support. -/
theorem hasFiniteLaurentSupport_unit : HasFiniteLaurentSupport k fun j ↦ (unit k j : Type u) :=
  (finite_iff _).1 (finite_unit k)

/-- The one-dimensional space `M = k` in degree `0`, as a finite graded vector space. -/
noncomputable abbrev unitFinite : (finite k).FullSubcategory :=
  ⟨unit k, finite_unit k⟩

/-! ### The graded dimension -/

/-- The graded dimension `gdim V = ∑ⱼ dim_k(Vⱼ) qʲ` of finite graded vector spaces, as an invariant
which is additive on conflations and turns the shift into multiplication by `q`. -/
private noncomputable def gradedDimensionInvariant :
    GradedExactStructure.ShiftInvariant (finiteExactStructure k)
      (laurentTAut ℤ (LaurentPolynomial ℤ)) where
  obj V := gradedDimension k (fun j ↦ (V.obj j : Type u)) V.property
  map_conflation S hS := by
    have hS' (j : ℤ) := ((finiteExactStructure_conflation_iff k S).1 hS).map_of_exact
      (GradedObject.eval j)
    exact gradedDimension_shortExact S.X₁.property S.X₃.property
      (fun j ↦ ((S.map (finite k).ι).f j).hom) (fun j ↦ ((S.map (finite k).ι).g j).hom)
      (fun j ↦ (hS' j).moduleCat_injective_f)
      (fun j ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS' j).exact)
      (fun j ↦ (hS' j).moduleCat_surjective_g)
  map_shift V := by
    rw [laurentTAut_apply, smul_eq_mul, ← neg_neg (1 : ℤ),
      ← gradedDimension_reindex_add V.property (-1)]
    exact gradedDimension_congr _ _ fun j ↦
      ((shiftObjApplyIso k V j).toLinearEquiv.finrank_eq).trans (by rw [sub_eq_add_neg])

private theorem gradedDimensionInvariant_obj (V : (finite k).FullSubcategory) :
    (gradedDimensionInvariant k).obj V =
      gradedDimension k (fun j ↦ (V.obj j : Type u)) ((finite_iff _).1 V.property) :=
  rfl

/-- The graded dimension of `M = k` in degree `0` is `1`. -/
@[simp]
theorem gradedDimension_unit :
    gradedDimension k (fun j ↦ (unit k j : Type u)) (hasFiniteLaurentSupport_unit k) = 1 := by
  rw [gradedDimension_eq_sum _ {0} fun j hj ↦
    ModuleCat.subsingleton_of_isZero (isZero_unit_obj k (by simpa using hj))]
  simp

/-! ### The graded Grothendieck group -/

/-- A nonzero vector in degree `0` spans a copy of `M`; splitting it off is a conflation
`M ↪ V ↠ C`. -/
private theorem exists_of_eq_add (V : (finite k).FullSubcategory) [Nontrivial (V.obj 0)] :
    ∃ C : (finite k).FullSubcategory,
      LaurentK0.of.{u} (finiteExactStructure k) V =
          LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k) +
            LaurentK0.of.{u} (finiteExactStructure k) C ∧
        (gradedDimensionInvariant k).obj V = 1 + (gradedDimensionInvariant k).obj C := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V.obj 0)
  let g : unit k ⟶ V.obj := (homUnitLinearEquiv k V.obj).symm v
  have : Mono g := GradedObject.mono_of_mono_apply g fun j ↦ by
    rw [ModuleCat.mono_iff_injective]
    by_cases hj : j = 0
    · subst hj
      intro a b hab
      simp only [g, homUnitLinearEquiv_symm_apply_zero, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply] at hab
      exact (unitObjZeroIso k).toLinearEquiv.injective (smul_left_injective k hv hab)
    · have := ModuleCat.subsingleton_of_isZero (isZero_unit_obj k hj)
      exact Function.injective_of_subsingleton _
  have hS := (ExactStructure.abelian_conflation _).1 (ExactStructure.abelian_conflation_of_mono g)
  have hC : finite k (cokernel g) := HasFiniteLaurentSupport.of_surjective V.property
    (fun j ↦ (cokernel.π g j).hom) fun j ↦
      (hS.map_of_exact (GradedObject.eval j)).moduleCat_surjective_g
  let T : ShortComplex (finite k).FullSubcategory :=
    ShortComplex.mk (X₁ := unitFinite k) (X₂ := V) (X₃ := ⟨cokernel g, hC⟩)
      (ObjectProperty.homMk g) (ObjectProperty.homMk (cokernel.π g))
      ((finite k).ι.map_injective (by simp))
  have hT : (finiteExactStructure k).Conflation T :=
    (finiteExactStructure_conflation_iff k T).2 hS
  refine ⟨T.X₃, LaurentK0.of_conflation.{u} _ hT, ?_⟩
  rw [(gradedDimensionInvariant k).map_conflation hT]
  congr 1
  exact gradedDimension_unit k

/-- The statement `[V] = gdim V · [M]` is invariant under the grading shift: both sides are
multiplied by `q`. -/
private theorem of_eq_smul_shift_iff (V : (finite k).FullSubcategory) :
    LaurentK0.of.{u} (finiteExactStructure k) ((finiteExactStructure k).shift.functor.obj V) =
        (gradedDimensionInvariant k).obj ((finiteExactStructure k).shift.functor.obj V) •
          LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k) ↔
      LaurentK0.of.{u} (finiteExactStructure k) V =
        (gradedDimensionInvariant k).obj V •
          LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k) := by
  rw [← LaurentK0.T_one_smul_of.{u}, (gradedDimensionInvariant k).map_shift, laurentTAut_apply,
    smul_assoc, (isUnit_T 1).smul_left_cancel]

/-- The statement `[V] = gdim V · [M]` is invariant under isomorphism. -/
private theorem of_eq_smul_iff_of_iso {V W : (finite k).FullSubcategory} (e : V ≅ W) :
    LaurentK0.of.{u} (finiteExactStructure k) V =
        (gradedDimensionInvariant k).obj V •
          LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k) ↔
      LaurentK0.of.{u} (finiteExactStructure k) W =
        (gradedDimensionInvariant k).obj W •
          LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k) := by
  rw [LaurentK0.of_congr.{u} _ e, (gradedDimensionInvariant k).map_iso e]

/-- The total dimension of a finite graded vector space is its graded dimension at `q = 1`. -/
private theorem finrank_directSum_eq (V : (finite k).FullSubcategory) :
    (Module.finrank k (⨁ j, (V.obj j : Type u)) : ℤ) =
      laurentEval (1 : ℤˣ) ((gradedDimensionInvariant k).obj V) :=
  (laurentEval_one_gradedDimension _).symm

/-- Isomorphic finite graded vector spaces have the same total dimension. -/
private theorem finrank_directSum_congr {V W : (finite k).FullSubcategory} (e : V ≅ W) :
    Module.finrank k (⨁ j, (V.obj j : Type u)) = Module.finrank k (⨁ j, (W.obj j : Type u)) := by
  rw [← Nat.cast_inj (R := ℤ), finrank_directSum_eq, finrank_directSum_eq,
    (gradedDimensionInvariant k).map_iso e]

/-- The grading shift does not change the total dimension. -/
private theorem finrank_directSum_shift (V : (finite k).FullSubcategory) :
    Module.finrank k (⨁ j, (((finiteExactStructure k).shift.functor.obj V).obj j : Type u)) =
      Module.finrank k (⨁ j, (V.obj j : Type u)) := by
  rw [← Nat.cast_inj (R := ℤ), finrank_directSum_eq, finrank_directSum_eq,
    (gradedDimensionInvariant k).map_shift, laurentTAut_apply, smul_eq_mul, map_mul,
    laurentEval_T]
  simp

/-- **Every class is a Laurent multiple of `[M]`**: `[V] = gdim V · [M]` in the graded
Grothendieck group of finite graded vector spaces. -/
theorem of_eq_gradedDimension_smul (V : (finite k).FullSubcategory) :
    LaurentK0.of.{u} (finiteExactStructure k) V =
      gradedDimension k (fun j ↦ (V.obj j : Type u)) ((finite_iff _).1 V.property) •
        LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k) := by
  rw [← gradedDimensionInvariant_obj]
  -- Strong induction on the total dimension.
  induction hn : Module.finrank k (⨁ j, (V.obj j : Type u)) using Nat.strong_induction_on
    generalizing V with
  | _ n ih =>
  -- A graded vector space with all pieces zero is a zero object, with graded dimension `0`.
  by_cases hzero : ∀ j, Subsingleton (V.obj j)
  · have hV : IsZero V := IsZero.of_full_of_faithful_of_isZero (finite k).ι V
      ((IsZero.iff_id_eq_zero _).2 (funext fun j ↦
        (ModuleCat.isZero_of_subsingleton (V.obj j)).eq_of_src _ _))
    have hgdim : (gradedDimensionInvariant k).obj V = 0 :=
      (gradedDimension_eq_zero_iff _).2 hzero
    rw [← LaurentK0.ofExactK0_exactK0_of.{u}, ExactK0.of_eq_zero_of_isZero.{u} hV, map_zero,
      hgdim, zero_smul]
  obtain ⟨i, hi⟩ := not_forall.1 hzero
  rw [not_subsingleton_iff_nontrivial] at hi
  clear hzero
  -- Shift a nonzero piece into degree `0`, then split off a copy of `M`.
  induction i using Int.induction_on generalizing V with
  | zero =>
    obtain ⟨C, hof, hdim⟩ := exists_of_eq_add k V
    have hlt : Module.finrank k (⨁ j, (C.obj j : Type u)) < n := by
      have := congrArg (laurentEval (1 : ℤˣ)) hdim
      rw [map_add, map_one, ← finrank_directSum_eq, ← finrank_directSum_eq, hn] at this
      omega
    rw [hof, hdim, ih _ hlt C rfl, add_smul, one_smul]
  | succ i hind =>
    let W := (finiteExactStructure k).shift.inverse.obj V
    let e : (finiteExactStructure k).shift.functor.obj W ≅ V :=
      (finiteExactStructure k).shift.counitIso.app V
    have hW : Nontrivial (W.obj i) := by
      have φ := Pi.isoApp ((finite k).ι.mapIso e).symm (i + 1) ≪≫ shiftObjApplyIso k W (i + 1)
      rw [add_sub_cancel_right] at φ
      exact @Equiv.nontrivial _ _ φ.symm.toLinearEquiv.toEquiv hi
    rw [← of_eq_smul_iff_of_iso k e, of_eq_smul_shift_iff]
    exact hind W (by rw [← finrank_directSum_shift, finrank_directSum_congr k e, hn]) hW
  | pred i hind =>
    let W := (finiteExactStructure k).shift.functor.obj V
    have hW : Nontrivial (W.obj (-i)) :=
      (shiftObjApplyIso k V (-i)).toLinearEquiv.toEquiv.nontrivial
    rw [← of_eq_smul_shift_iff]
    exact hind W (by rw [finrank_directSum_shift, hn]) hW

/-- **The graded Grothendieck group of finite graded vector spaces is `ℤ[q,q⁻¹]`**, by the graded
dimension `[V] ↦ gdim V = ∑ⱼ dim_k(Vⱼ) qʲ`. The inverse sends a Laurent polynomial `p` to
`p · [M]`, for `M = k` placed in degree `0`. -/
noncomputable def laurentK0Equiv :
    LaurentK0.{u} (finiteExactStructure k) ≃ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  LinearEquiv.ofLinearMap (LaurentK0.lift _ (gradedDimensionInvariant k))
    (LinearMap.toSpanSingleton _ _ (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)))
    (LinearMap.ext_ring (by simp [gradedDimensionInvariant_obj]))
    (LaurentK0.hom_ext.{u} _ fun V ↦ by
      simpa [gradedDimensionInvariant_obj] using (of_eq_gradedDimension_smul k V).symm)

/-- The graded dimension of the class of `V` is `gdim V`. -/
@[simp]
theorem laurentK0Equiv_of (V : (finite k).FullSubcategory) :
    laurentK0Equiv k (LaurentK0.of.{u} (finiteExactStructure k) V) =
      gradedDimension k (fun j ↦ (V.obj j : Type u)) ((finite_iff _).1 V.property) := by
  simp [laurentK0Equiv, gradedDimensionInvariant_obj]

/-- The inverse of the graded dimension sends `p` to `p · [M]`. -/
@[simp]
theorem laurentK0Equiv_symm_apply (p : LaurentPolynomial ℤ) :
    (laurentK0Equiv k).symm p = p • LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k) := by
  simp [laurentK0Equiv]

/-! ### Specializations of the graded Grothendieck group -/

/-- The specialization of the graded Grothendieck group of finite graded vector spaces at `q = ε`
is free of rank one, on the class of `M = k` placed in degree `0`. -/
noncomputable def laurentSpecializationBasis (ε : ℤˣ) :
    Module.Basis Unit ℤ (LaurentSpecialization ε (LaurentK0.{u} (finiteExactStructure k))) :=
  LaurentSpecialization.basis ε
    ((Module.Basis.singleton Unit (LaurentPolynomial ℤ)).map (laurentK0Equiv k).symm)

/-- The vector of `TauCeti.GradedVectorSpace.laurentSpecializationBasis` is the specialized class
of `M`. -/
@[simp]
theorem laurentSpecializationBasis_apply (ε : ℤˣ) (i : Unit) :
    laurentSpecializationBasis k ε i =
      LaurentSpecialization.mk ε (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)) := by
  simp [laurentSpecializationBasis]

/-- The coordinate of a specialized class is its graded dimension evaluated at `q = ε`. -/
@[simp]
theorem laurentSpecializationBasis_repr_mk (ε : ℤˣ)
    (x : LaurentK0.{u} (finiteExactStructure k)) (i : Unit) :
    (laurentSpecializationBasis k ε).repr (LaurentSpecialization.mk ε x) i =
      laurentEval ε (laurentK0Equiv k x) := by
  simp [laurentSpecializationBasis]

/-- **At `q = -1` a single shift changes the class**: the specialized class of `M{1}`, which is
`-[M]` by `TauCeti.LaurentK0.mk_of_shift_functor_obj`, differs from that of `M`. -/
theorem mk_neg_one_of_shift_unitFinite_ne :
    LaurentSpecialization.mk (-1 : ℤˣ) (LaurentK0.of.{u} (finiteExactStructure k)
        ((finiteExactStructure k).shift.functor.obj (unitFinite k))) ≠
      LaurentSpecialization.mk (-1 : ℤˣ)
        (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)) := by
  intro h
  have := congrArg (fun x ↦ (laurentSpecializationBasis k (-1 : ℤˣ)).repr x ()) h
  simp at this

end GradedVectorSpace

end TauCeti
