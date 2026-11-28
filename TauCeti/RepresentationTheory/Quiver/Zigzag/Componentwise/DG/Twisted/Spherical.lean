/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import TauCeti.CategoryTheory.DG.Spherical
public import TauCeti.GroupTheory.Coxeter.DeformedReflection
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Duality

/-!
# `2`-sphericality and `A_m`-configurations of zigzag projectives

Over a Noetherian commutative ring, all pairs in `TauCeti.ZigzagProjectiveTwistedClosure` satisfy
`TauCeti.HasFiniteTotalGradedHom` (`hasFiniteTotalGradedHom`), and `vertexObject` identifies vertex
cohomology multiplicatively with zigzag algebra corners (`vertexObjectHomologyEquivCorner`,
`vertexObjectHomologyEquivCorner_dgHomologyClass`,
`coe_vertexObjectHomologyEquivCorner_dgHomologyComp`). Over any field `k` and finite simple graph
`G`, every `vertexObject k G i` and its shifts are `2`-spherical, any `SimpleGraph.pathGraph m ≃g G`
gives an `A_m`-configuration, and `eulerMatrix` coincides with the field-free Cartan matrix
`SimpleGraph.graphCartanMatrix G ℤ = (2 : ℤ) • 1 - G.adjMatrix ℤ`
(`eulerMatrix_eq_graphCartanMatrix`), identifying numerical Seidel–Thomas twists with
`SimpleGraph.deformedReflection G (-1 : ℤˣ)`
(`deformedReflection_neg_one_single_eq_sub_dgEulerPairing`).

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*, §2, §4.
* R. Rouquier and A. Zimmermann, *Picard groups for derived module categories*, Section 4.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.ZigzagProjectiveTwistedClosure

universe u

variable (k : Type u) {V : Type u} (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "A" => zigzagAlgebraIntegerGrade k G
local notation "𝒱" => DGFullSubcategory (fun M ↦ ∃ i : V, M = D i)
local notation "𝒮" => DGShiftClosure 𝒱
local notation "𝒜" => DGAdditiveClosure 𝒮

section CommRing

variable [Finite V] [CommRing k]

/-- The canonical DG functor embedding the zero-DG vertex subcategory `𝒱` into
`ZigzagProjectiveTwistedClosure k G` as unshifted one-summand objects with zero twist. -/
-- Exposed so `(vertexEmbedding k G).obj` reduces definitionally to the three-step composite object
-- in `dgMap_vertexEmbedding` and `vertexObjectDGHomEquiv`.
@[expose] def vertexEmbedding :
    EnrichedFunctor (CochainComplex (ModuleCat.{u} k) ℤ) 𝒱 (ZigzagProjectiveTwistedClosure k G) :=
  ((DGShiftClosure.ι k).comp (CochainComplex (ModuleCat.{u} k) ℤ)
    (DGAdditiveClosure.embedding k)).comp (CochainComplex (ModuleCat.{u} k) ℤ)
    (DGTwistedObject.embedding k)

/-- `vertexEmbedding` is quasi-fully faithful. -/
theorem isQuasiFullyFaithful_vertexEmbedding : (vertexEmbedding k G).IsQuasiFullyFaithful :=
  ((EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGShiftClosure.ι k (C := 𝒱)) fun _ _ ↦ inferInstance).comp
    (EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGAdditiveClosure.embedding k (C := 𝒮)) fun _ _ ↦ inferInstance)).comp
    (EnrichedFunctor.isQuasiFullyFaithful_of_isIso_map
      (F := DGTwistedObject.embedding k (C := 𝒜)) fun _ _ ↦ inferInstance)

/-- The canonical object of `ZigzagProjectiveTwistedClosure k G` associated to vertex `i : V`. -/
-- Exposed so `(vertexEmbedding k G).obj ⟨D i, i, rfl⟩` has type `vertexObject k G i` in
-- `vertexObjectDGHomEquiv_symm_apply`.
@[expose] def vertexObject (i : V) : ZigzagProjectiveTwistedClosure k G :=
  (vertexEmbedding k G).obj ⟨D i, i, rfl⟩

/-- `vertexObject k G i` unfolds to the one-summand unshifted object with zero twist. -/
theorem vertexObject_eq (i : V) :
    vertexObject k G i = DGTwistedObject.ofObj k ⟨PUnit, fun _ ↦ ⟨⟨D i, i, rfl⟩, 0⟩⟩ := by
  simp [vertexObject, vertexEmbedding]

/-- Chain-level linear equivalence unpacking homogeneous degree-`d` morphisms between
`vertexObject k G i` and `vertexObject k G j` into homogeneous morphisms `D i ⟶ D j`. -/
def vertexObjectDGHomEquiv (i j : V) (d : ℤ) :
    DGHom k d (vertexObject k G i) (vertexObject k G j) ≃ₗ[k] DGHom k d (D i) (D j) :=
  let u : 𝒱 := ⟨D i, i, rfl⟩; let w : 𝒱 := ⟨D j, j, rfl⟩
  (((DGShiftClosure.ιHomEquiv k u w d).trans
    (DGAdditiveClosure.embeddingHomEquiv k ((DGShiftClosure.ι k).obj u)
      ((DGShiftClosure.ι k).obj w) d)).trans
    (DGTwistedObject.embeddingHomEquiv k _ _ d)).symm

/-- `vertexEmbedding` acts on homogeneous morphisms by composing the three embedding
equivalences. -/
@[simp] theorem dgMap_vertexEmbedding {u w : 𝒱} (d : ℤ) (g : DGHom k d u w) :
    (vertexEmbedding k G).dgMap d g =
      DGTwistedObject.embeddingHomEquiv k _ _ d
        (DGAdditiveClosure.embeddingHomEquiv k _ _ d (DGShiftClosure.ιHomEquiv k u w d g)) := by
  unfold vertexEmbedding
  exact (((DGShiftClosure.ι k (C := 𝒱)).comp (CochainComplex (ModuleCat.{u} k) ℤ)
    (DGAdditiveClosure.embedding k)).comp_dgMap (DGTwistedObject.embedding k) g).trans <|
    (congrArg ((DGTwistedObject.embedding k).dgMap d)
      ((DGShiftClosure.ι k (C := 𝒱)).comp_dgMap (DGAdditiveClosure.embedding k) g)).trans <|
      (DGTwistedObject.dgMap_embedding k _).trans <|
        congrArg (DGTwistedObject.embeddingHomEquiv k _ _ d) <|
          (DGAdditiveClosure.dgMap_embedding k _).trans <|
            congrArg (DGAdditiveClosure.embeddingHomEquiv k _ _ d) (DGShiftClosure.dgMap_ι k g)

/-- The inverse of `vertexObjectDGHomEquiv` is the action of `vertexEmbedding` on homogeneous
morphisms. -/
@[simp] theorem vertexObjectDGHomEquiv_symm_apply (i j : V) (d : ℤ)
    (g : DGHom k d (D i) (D j)) :
    (vertexObjectDGHomEquiv k G i j d).symm g =
      (vertexEmbedding k G).dgMap (X := ⟨D i, i, rfl⟩) (Y := ⟨D j, j, rfl⟩) d g := by
  -- `DGFullSubcategory.dgHomComplex_eq` identifies `DGHom k d (⟨D i, i, rfl⟩ : 𝒱) ⟨D j, j, rfl⟩`
  -- with `DGHom k d (D i) (D j)`, and `vertexObject` is exposed as `(vertexEmbedding k G).obj …`.
  simp only [dgMap_vertexEmbedding]
  rfl

/-- `vertexObjectDGHomEquiv` commutes with homogeneous DG composition `TauCeti.dgComp`. -/
theorem vertexObjectDGHomEquiv_dgComp (i j l : V) {p q n : ℤ} (h : p + q = n)
    (f : DGHom k p (vertexObject k G i) (vertexObject k G j))
    (g : DGHom k q (vertexObject k G j) (vertexObject k G l)) :
    vertexObjectDGHomEquiv k G i l n (dgComp k f g h) =
      dgComp k (vertexObjectDGHomEquiv k G i j p f) (vertexObjectDGHomEquiv k G j l q g) h := by
  obtain ⟨f₀, rfl⟩ := (vertexObjectDGHomEquiv k G i j p).symm.surjective f
  obtain ⟨g₀, rfl⟩ := (vertexObjectDGHomEquiv k G j l q).symm.surjective g
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  apply (vertexObjectDGHomEquiv k G i l n).symm.injective
  simp only [LinearEquiv.symm_apply_apply, vertexObjectDGHomEquiv_symm_apply,
    ← DGFullSubcategory.dgComp_eq k
      (X := (⟨D i, i, rfl⟩ : 𝒱)) (Y := (⟨D j, j, rfl⟩ : 𝒱)) (Z := (⟨D l, l, rfl⟩ : 𝒱))]
  exact ((vertexEmbedding k G).dgMap_dgComp
    (X := (⟨D i, i, rfl⟩ : 𝒱)) (Y := (⟨D j, j, rfl⟩ : 𝒱)) (Z := (⟨D l, l, rfl⟩ : 𝒱))
    f₀ g₀ h).symm

/-- Canonical cohomology between `vertexObject k G i` and `vertexObject k G j` in degree `d`
identifies linearly with the signed graded corner `e_i Z e_j ∩ Z_d` of the zigzag algebra. -/
def vertexObjectHomologyEquivCorner (i j : V) (d : ℤ) :
    (dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d ≃ₗ[k]
      ↥(cornerSubmodule k (e i) (e j) ⊓ A d) :=
  let u : 𝒱 := ⟨D i, i, rfl⟩; let w : 𝒱 := ⟨D j, j, rfl⟩
  (((isQuasiFullyFaithful_vertexEmbedding k G).homologyLinearEquiv u w d).symm.trans
    (eqToIso (congrArg (fun K ↦ K.homology d)
      (DGFullSubcategory.dgHomComplex_eq (R := k) u w))).toLinearEquiv).trans
    (((dgHomologyCastEquiv k (D i) (D j) (neg_neg d).symm).trans
      (zigzagAlgebraProjectiveHomologyEquivCorner k G i j (-d))).trans
      (LinearEquiv.ofEq _ _ (by rw [neg_neg])))

/-- `vertexObjectHomologyEquivCorner` unpacks cohomology through `vertexEmbedding`, full-subcategory
identification, degree negation, and `zigzagAlgebraProjectiveHomologyEquivCorner`. -/
theorem vertexObjectHomologyEquivCorner_apply (i j : V) (d : ℤ)
    (x : (dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d) :
    vertexObjectHomologyEquivCorner k G i j d x =
      LinearEquiv.ofEq _ _ (by rw [neg_neg])
        (zigzagAlgebraProjectiveHomologyEquivCorner k G i j (-d)
          (dgHomologyCastEquiv k (D i) (D j) (neg_neg d).symm
            ((eqToIso (congrArg (fun K ↦ K.homology d)
              (DGFullSubcategory.dgHomComplex_eq (R := k)
                ⟨D i, i, rfl⟩ ⟨D j, j, rfl⟩))).toLinearEquiv
              (((isQuasiFullyFaithful_vertexEmbedding k G).homologyLinearEquiv
                ⟨D i, i, rfl⟩ ⟨D j, j, rfl⟩ d).symm x)))) :=
  (rfl)

private theorem homologyLinearEquiv_vertexEmbedding_symm_dgHomologyClass (i j : V) (d : ℤ)
    (f : DGHom k d ((vertexEmbedding k G).obj ⟨D i, i, rfl⟩)
      ((vertexEmbedding k G).obj ⟨D j, j, rfl⟩))
    (hf : dgDifferential k d f = 0) :
    ((isQuasiFullyFaithful_vertexEmbedding k G).homologyLinearEquiv
        ⟨D i, i, rfl⟩ ⟨D j, j, rfl⟩ d).symm (dgHomologyClass k f hf) =
      dgHomologyClass k (X := (⟨D i, i, rfl⟩ : 𝒱)) (Y := (⟨D j, j, rfl⟩ : 𝒱))
        (vertexObjectDGHomEquiv k G i j d f) (by simp) := by
  let u : 𝒱 := ⟨D i, i, rfl⟩; let w : 𝒱 := ⟨D j, j, rfl⟩
  let f₀ : DGHom k d (D i) (D j) := vertexObjectDGHomEquiv k G i j d f
  rw [LinearEquiv.symm_apply_eq, EnrichedFunctor.IsQuasiFullyFaithful.homologyLinearEquiv_apply,
    homologyMap_dgHomologyClass]
  refine dgHomologyClass_congr k _ _ ?_
  exact (((vertexObjectDGHomEquiv k G i j d).symm_apply_apply f).symm.trans
    (vertexObjectDGHomEquiv_symm_apply k G i j d f₀)).trans
    ((vertexEmbedding k G).dgMap_apply (X := u) (Y := w) f₀)

private theorem fullSubcategory_dgHomologyClass_eq (i j : V) (d : ℤ)
    (f₀ : DGHom k d (D i) (D j))
    (hf₀ : dgDifferential k (X := (⟨D i, i, rfl⟩ : 𝒱)) (Y := (⟨D j, j, rfl⟩ : 𝒱)) d f₀ = 0)
    (hf₀' : dgDifferential k (X := D i) (Y := D j) d f₀ = 0) :
    (eqToIso (congrArg (fun K ↦ K.homology d)
        (DGFullSubcategory.dgHomComplex_eq (R := k)
          (⟨D i, i, rfl⟩ : 𝒱) ⟨D j, j, rfl⟩))).toLinearEquiv
        (dgHomologyClass k (X := (⟨D i, i, rfl⟩ : 𝒱)) (Y := (⟨D j, j, rfl⟩ : 𝒱)) f₀ hf₀) =
      dgHomologyClass k (X := D i) (Y := D j) f₀ hf₀' := by
  obtain ⟨z₀, hz₀, hclass₀⟩ :=
    exists_iCycles_and_dgHomologyClass k (X := D i) (Y := D j) f₀ hf₀'
  simp only [eqToIso_refl, Iso.toLinearEquiv_apply, Iso.refl_hom, ModuleCat.id_apply]
  exact (dgHomologyClass_eq_homologyπ k
    (X := (⟨D i, i, rfl⟩ : 𝒱)) (Y := (⟨D j, j, rfl⟩ : 𝒱)) hf₀ z₀ hz₀).trans hclass₀.symm

/-- On `TauCeti.dgHomologyClass`, `vertexObjectHomologyEquivCorner` evaluates
`zigzagAlgebraProjectiveDGHomEquivCornerOfDegree` on the unpacked morphism
`vertexObjectDGHomEquiv k G i j d f`. -/
@[simp] theorem vertexObjectHomologyEquivCorner_dgHomologyClass (i j : V) (d : ℤ)
    (f : DGHom k d (vertexObject k G i) (vertexObject k G j)) (hf : dgDifferential k d f = 0) :
    vertexObjectHomologyEquivCorner k G i j d (dgHomologyClass k f hf) =
      zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G i j d
        (vertexObjectDGHomEquiv k G i j d f) := by
  -- First unpack the quasi-equivalence and full-subcategory steps on `dgHomologyClass`, unfolding
  -- semireducible `vertexObject` so `rw` matches `(vertexEmbedding k G).obj …`.
  rw [vertexObjectHomologyEquivCorner_apply]
  dsimp only [vertexObject] at f hf ⊢
  rw [homologyLinearEquiv_vertexEmbedding_symm_dgHomologyClass k G i j d f hf,
    fullSubcategory_dgHomologyClass_eq k G i j d (vertexObjectDGHomEquiv k G i j d f)
      (by simp) (by simp),
    dgHomologyCastEquiv_dgHomologyClass]
  -- Lift the degree-cast cocycle once via `exists_iCycles_and_dgHomologyClass` to evaluate the
  -- corner homology equivalence on `homologyπ`.
  obtain ⟨z, hz, hclass⟩ := exists_iCycles_and_dgHomologyClass k (X := D i) (Y := D j)
    (castDeg k (neg_neg d).symm (vertexObjectDGHomEquiv k G i j d f)) (by simp)
  rw [hclass, zigzagAlgebraProjectiveHomologyEquivCorner_homologyπ, hz]
  apply Subtype.ext
  rw [LinearEquiv.coe_ofEq_apply, coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_apply]
  -- Both sides apply `zigzagAlgebraProjectiveDGHomEquivCorner k G i j (-d)` to `castDeg` along
  -- proof-irrelevant witnesses `(neg_neg d).symm` and `(Int.neg_neg d).symm` of `d = - -d`.
  exact congrArg (fun g ↦ (zigzagAlgebraProjectiveDGHomEquivCorner k G i j (-d) g :
    AlgCat.carrier (zigzagAlgebra k G))) rfl

/-- `vertexObjectHomologyEquivCorner` intertwines graded cohomology composition
`TauCeti.dgHomologyComp` with multiplication in the zigzag algebra. -/
@[simp] theorem coe_vertexObjectHomologyEquivCorner_dgHomologyComp
    (i j l : V) {p q n : ℤ} (hpq : p + q = n)
    (x : (dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology p)
    (y : (dgHomComplex k (vertexObject k G j) (vertexObject k G l)).homology q) :
    (vertexObjectHomologyEquivCorner k G i l n
        (dgHomologyComp k (vertexObject k G i) (vertexObject k G j)
          (vertexObject k G l) hpq x y) :
        AlgCat.carrier (zigzagAlgebra k G)) =
      (vertexObjectHomologyEquivCorner k G i j p x : AlgCat.carrier (zigzagAlgebra k G)) *
        (vertexObjectHomologyEquivCorner k G j l q y : AlgCat.carrier (zigzagAlgebra k G)) := by
  obtain ⟨f, hf, rfl⟩ := exists_dgHomologyClass_eq k x
  obtain ⟨g, hg, rfl⟩ := exists_dgHomologyClass_eq k y
  rw [dgHomologyComp_dgHomologyClass, vertexObjectHomologyEquivCorner_dgHomologyClass,
    vertexObjectHomologyEquivCorner_dgHomologyClass,
    vertexObjectHomologyEquivCorner_dgHomologyClass, vertexObjectDGHomEquiv_dgComp,
    coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_comp]

/-- Self-cohomology of `vertexObject k G i` vanishes in every degree `d ∉ {0, 2}`. -/
theorem subsingleton_homology_vertexObject_self_of_ne (i : V) {d : ℤ}
    (hd0 : d ≠ 0) (hd2 : d ≠ 2) :
    Subsingleton ((dgHomComplex k (vertexObject k G i) (vertexObject k G i)).homology d) := by
  refine (vertexObjectHomologyEquivCorner k G i i d).toEquiv.subsingleton_congr.mpr ?_
  rw [cornerSubmodule_zigzagAlgebra_self_inf_integerGrade]; simp only [hd0, hd2, ↓reduceIte]
  infer_instance

/-- Cohomology between two vertex objects vanishes outside degrees `{0, 1, 2}`. -/
theorem subsingleton_homology_vertexObject_of_not_mem (i j : V) {d : ℤ}
    (hd : d ∉ ({0, 1, 2} : Finset ℤ)) :
    Subsingleton ((dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  rcases hd with ⟨hd0, hd1, hd2⟩
  by_cases hij : i = j
  · exact hij ▸ subsingleton_homology_vertexObject_self_of_ne k G i hd0 hd2
  · refine (vertexObjectHomologyEquivCorner k G i j d).toEquiv.subsingleton_congr.mpr ?_
    have hbot : cornerSubmodule k (e i) (e j) ⊓ A d = ⊥ := by
      by_cases hadj : G.Adj j i
      · rw [cornerSubmodule_zigzagAlgebra_inf_integerGrade_of_adj k G hadj]; simp [hd1]
      · rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij (fun h ↦ hadj h.symm),
          bot_inf_eq]
    rw [hbot]; infer_instance

/-- Every pair of formal twisted objects in `ZigzagProjectiveTwistedClosure k G` satisfies
`TauCeti.HasFiniteTotalGradedHom` over a Noetherian commutative coefficient ring. -/
theorem hasFiniteTotalGradedHom [IsNoetherianRing k]
    (X Y : ZigzagProjectiveTwistedClosure k G) : HasFiniteTotalGradedHom k X Y :=
  HasFiniteTotalGradedHom.of_finset k (homSupport k G X Y)
    (subsingleton_homology_of_not_mem_homSupport k G X Y)

end CommRing

section Field

variable [Finite V] [Field k]

open scoped Classical in
/-- Over a field `k`, `finrank Hom^d(vertexObject i, vertexObject j)` is `1` in degrees `0, 2`
when `i = j`, `1` in degree `1` when `G.Adj i j`, and `0` otherwise. -/
@[simp] theorem finrank_homology_vertexObject (i j : V) (d : ℤ) :
    Module.finrank k ((dgHomComplex k (vertexObject k G i) (vertexObject k G j)).homology d) =
      if i = j then if d = 0 ∨ d = 2 then 1 else 0
      else if G.Adj i j ∧ d = 1 then 1 else 0 :=
  (vertexObjectHomologyEquivCorner k G i j d).finrank_eq.trans
    (finrank_cornerSubmodule_zigzagAlgebra_inf_integerGrade k G i j d)

open scoped Classical in
/-- Total graded `Hom` dimension between vertex objects is `2` on the diagonal, `1` on edges, and
`0` on non-edges. -/
@[simp] theorem dgTotalHomFinrank_vertexObject (i j : V) :
    dgTotalHomFinrank k (vertexObject k G i) (vertexObject k G j) =
      if i = j then 2 else if G.Adj i j then 1 else 0 := by
  classical
  rw [dgTotalHomFinrank_eq_sum k ({0, 1, 2} : Finset ℤ)
      (fun _ ↦ subsingleton_homology_vertexObject_of_not_mem k G i j),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;> simp [hij, hadj]

open scoped Classical in
/-- The graded Euler pairing `χ(vertexObject i, vertexObject j)` equals the symmetric generalized
Cartan pairing of `G`: `2` on the diagonal, `-1` on edges, and `0` on non-edges. -/
@[simp] theorem dgEulerPairing_vertexObject (i j : V) :
    dgEulerPairing k (vertexObject k G i) (vertexObject k G j) =
      if i = j then 2 else if G.Adj i j then -1 else 0 := by
  classical
  rw [dgEulerPairing_eq_sum k ({0, 1, 2} : Finset ℤ)
      (fun _ ↦ subsingleton_homology_vertexObject_of_not_mem k G i j),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rcases (by decide : (0 : ℤ).negOnePow = 1 ∧ (1 : ℤ).negOnePow = -1 ∧ (2 : ℤ).negOnePow = 1)
    with ⟨hp0, hp1, hp2⟩
  rw [hp0, hp1, hp2]
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;> simp [hij, hadj]

/-- Every `vertexObject k G i` is unconditionally a Seidel–Thomas `2`-spherical object over a field
`k`, for **every** finite simple graph `G`. -/
theorem isSphericalObject_vertexObject (i : V) :
    IsSphericalObject k 2 (vertexObject k G i) where
  pos := by decide
  hasFiniteTotalGradedHom_from := hasFiniteTotalGradedHom k G (vertexObject k G i)
  finrank_homology_zero := by simp
  finrank_homology_top := by simp
  subsingleton_homology_of_ne := subsingleton_homology_vertexObject_self_of_ne k G i
  exists_trace_isPerfPair := by
    let v : (vertexObject k G i).obj.ι → V := fun _ ↦ i
    have hv : ∀ u, ((vertexObject k G i).obj.X u).obj.obj = D (v u) := by
      dsimp only [v]; rw [vertexObject_eq]; intro _; rfl
    have hc : ∀ u₁ u₂ : (vertexObject k G i).obj.ι,
        G.Adj (v u₁) (v u₂) → ((1 : kˣ) : k) = -((1 : kˣ) : k) :=
      fun _ _ hadj ↦ False.elim (G.ne_of_adj hadj rfl)
    refine ⟨homologyTrace k G (fun _ ↦ ((1 : kˣ) : k)) (vertexObject k G i) v hv hc, fun F d ↦ ?_⟩
    rw [← homologyPairing_eq_compr₂_homologyTrace]
    exact isPerfPair_homologyPairing k G (fun _ ↦ 1) (vertexObject k G i) F v hv hc d

/-- Every integer shift `(shiftFunctor k m).obj (vertexObject k G i)` is `2`-spherical. -/
theorem isSphericalObject_shiftFunctor_vertexObject (m : ℤ) (i : V) :
    IsSphericalObject k 2 ((DGTwistedObject.shiftFunctor k m).obj (vertexObject k G i)) :=
  (DGTwistedObject.isSphericalObject_shiftFunctor_iff 2 m (vertexObject k G i)).mpr
    (isSphericalObject_vertexObject k G i)

/-- Along any graph isomorphism `φ : SimpleGraph.pathGraph m ≃g G`, `fun i ↦ vertexObject k G (φ i)`
forms a Seidel–Thomas `A_m`-configuration of `2`-spherical objects. -/
theorem isAmSphericalConfiguration_of_pathGraphIso {m : ℕ} (φ : SimpleGraph.pathGraph m ≃g G) :
    IsAmSphericalConfiguration k m 2 (fun i ↦ vertexObject k G (φ i)) where
  isSphericalObject i := isSphericalObject_vertexObject k G (φ i)
  dgTotalHomFinrank_of_adj {i j} hadj := by
    have hadjG : G.Adj (φ i) (φ j) := φ.map_adj_iff.mpr (SimpleGraph.pathGraph_adj.mpr hadj)
    simp [dgTotalHomFinrank_vertexObject, G.ne_of_adj hadjG, hadjG]
  dgTotalHomFinrank_of_nonadj {i j} hne hnadj := by
    have hnadjG : ¬ G.Adj (φ i) (φ j) := by rwa [φ.map_adj_iff, SimpleGraph.pathGraph_adj]
    simp [dgTotalHomFinrank_vertexObject, hne, hnadjG]

/-- The `V × V` integer matrix of the graded Euler pairing `χ(vertexObject i, vertexObject j)`. -/
def eulerMatrix : Matrix V V ℤ :=
  Matrix.of fun i j ↦ dgEulerPairing k (vertexObject k G i) (vertexObject k G j)

/-- Entry `(i, j)` of `eulerMatrix k G` is `dgEulerPairing k (vertexObject i) (vertexObject j)`. -/
@[simp] theorem eulerMatrix_apply (i j : V) :
    eulerMatrix k G i j = dgEulerPairing k (vertexObject k G i) (vertexObject k G j) := (rfl)

/-- `eulerMatrix k G` coincides with the field-free generalized Cartan matrix
`SimpleGraph.graphCartanMatrix G ℤ`. -/
theorem eulerMatrix_eq_graphCartanMatrix [DecidableEq V] [DecidableRel G.Adj] :
    eulerMatrix k G = G.graphCartanMatrix ℤ := by
  ext i j
  rw [eulerMatrix_apply, dgEulerPairing_vertexObject, SimpleGraph.graphCartanMatrix_apply]
  -- Reconcile `Classical` decidability in `dgEulerPairing_vertexObject` with the given instances.
  by_cases hij : i = j <;> by_cases hadj : G.Adj i j <;> simp [hij, hadj]

/-- At `q = -1`, `SimpleGraph.deformedReflection G (-1 : ℤˣ) r` acts on the standard basis vector
`Pi.single j 1` by the Seidel–Thomas numerical twist formula
`[E_j] ↦ [E_j] - χ(E_r, E_j) [E_r]`. -/
theorem deformedReflection_neg_one_single_eq_sub_dgEulerPairing [Fintype V] [DecidableEq V]
    (r j : V) :
    G.deformedReflection (-1 : ℤˣ) r (Pi.single j 1) =
      Pi.single j 1 -
        dgEulerPairing k (vertexObject k G r) (vertexObject k G j) • Pi.single r 1 := by
  let _ := Classical.decRel G.Adj
  rw [G.deformedReflection_apply, Units.val_neg, Units.val_one, G.deformedCartanRow_neg_one_single,
    ← eulerMatrix_eq_graphCartanMatrix (k := k), eulerMatrix_apply]

open scoped Classical Matrix in
/-- `eulerMatrix k G` is symmetric (`(eulerMatrix k G)ᵀ = eulerMatrix k G`). -/
@[simp] theorem transpose_eulerMatrix : (eulerMatrix k G)ᵀ = eulerMatrix k G := by
  ext i j; simp [eq_comm, SimpleGraph.adj_comm]

end Field

/-- For `SimpleGraph.pathGraph m` over a `Type`-level field `k`, the vertex objects form a
Seidel–Thomas `A_m`-configuration of `2`-spherical objects. -/
theorem isAmSphericalConfiguration_vertexObject (k : Type) [Field k] (m : ℕ) :
    IsAmSphericalConfiguration k m 2 (vertexObject k (SimpleGraph.pathGraph m)) :=
  isAmSphericalConfiguration_of_pathGraphIso k (SimpleGraph.pathGraph m) SimpleGraph.Iso.refl

end TauCeti.ZigzagProjectiveTwistedClosure
