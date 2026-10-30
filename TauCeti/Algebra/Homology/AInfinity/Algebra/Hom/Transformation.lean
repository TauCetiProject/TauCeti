/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy

/-!
# The complex of transformations between A-infinity morphisms

Let `f g : A ⟶ B` be morphisms of `A∞` algebras, with bar maps `F` and `G` between the reduced bar
constructions `Tᶜ(sA)` and `Tᶜ(sB)`.  Following Lyubashenko, a *transformation* of degree `p` from
`f` to `g` is an `(F, G)`-coderivation of degree `p`: a linear map `D : Tᶜ(sA) ⟶ Tᶜ(sB)` raising
the suspended total degree by `p` and satisfying

`Δ ∘ D = (D ⊗ G) ∘ Δ + (F ⊗ D) ∘ (τ ⊗ 1) ∘ Δ`,

with `τ` the letterwise Koszul twist of parameter `p` of `Tᶜ(sA)`.  Such a map is determined by its
suspended Taylor components `π ∘ D`, the components `Dₙ : A^{⊗ n} ⟶ B` of degree `p - n + 1` of
the transformation.  The differential of a transformation is its graded commutator with the bar
differentials,

`δD = b_B ∘ D - (-1)^p D ∘ b_A`,

which is again a transformation, of degree `p + 1`, because `F` and `G` intertwine the bar
differentials; `δ² = 0` because `b_A² = 0` and `b_B² = 0`.  These transformations and their
differential form the cochain complex of `R`-modules `AInfinityHom.transformationComplex f g`.
This is the one-object case of Lyubashenko's complex of `A∞` transformations between `A∞`
functors, the morphism complexes of the `A∞` category of `A∞` functors; the composition of
transformations, which would make that category, is not constructed here.  The sign of the
differential is that of the morphism complexes of right `A∞` modules,
`TauCeti.AInfinityRightModule.homDifferential`.

The existing notions sit inside this complex.  The difference `F - G` of the bar maps is a closed
transformation of degree zero, and a homotopy from `f` to `g` is exactly a transformation of
degree `-1` whose differential is `F - G`; so `f` and `g` are homotopic exactly when `F - G` is a
coboundary.  Composing with an `A∞` morphism on either side maps transformations to
transformations and commutes with the differential, extending the composition of homotopies with
morphisms.

## Main definitions

* `TauCeti.AInfinityHom.transformationCochains`: the transformations of degree `p` from `f` to
  `g`, the `(F, G)`-coderivations of degree `p`.
* `TauCeti.AInfinityHom.transformationCochains.taylor`: the suspended Taylor components of a
  transformation.
* `TauCeti.AInfinityHom.transformationDifferential`: the graded commutator with the bar
  differentials.
* `TauCeti.AInfinityHom.transformationComplex`: the complex of transformations from `f` to `g`.
* `TauCeti.AInfinityHom.transformationCochains.compRight` and
  `TauCeti.AInfinityHom.transformationCochains.compLeft`: composition of transformations with an
  `A∞` morphism after or before them.
* `TauCeti.AInfinityHom.Homotopy.equivCochains`: homotopies from `f` to `g` are the
  transformations of degree `-1` bounding `F - G`.

## Main results

* `TauCeti.AInfinityHom.transformationCochains.ext`: a transformation is determined by its Taylor
  components.
* `TauCeti.AInfinityHom.transformationDifferential_transformationDifferential`: the differential
  squares to zero.
* `TauCeti.AInfinityHom.transformationCochains.taylor_transformationDifferential`: the Taylor
  components of the differential of a transformation.
* `TauCeti.AInfinityHom.transformationDifferential_barMap_sub_barMap`: the difference of the bar
  maps is a closed transformation of degree zero.
* `TauCeti.AInfinityHom.transformationDifferential_compRight` and
  `TauCeti.AInfinityHom.transformationDifferential_compLeft`: composition with a morphism commutes
  with the differential.

## References

* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), Sections 1--2, for `A∞` transformations as coderivations along a pair of `A∞` functors
  and their differential.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7, for homotopies.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

namespace AInfinityHom

variable (f g : AInfinityHom AA BB)

/-- The transformations of degree `p` from the `A∞` morphism `f` to the `A∞` morphism `g`: the
linear maps of reduced bar constructions of degree `p` for the suspended gradings which are
coderivations along the bar maps of `f` and `g` with twist parameter `p`. -/
def transformationCochains (p : ℤ) :
    Submodule R (ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) where
  carrier := {D |
    ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) p f.barMap g.barMap D ∧
      LinearMap.IsHomogeneous D (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
        (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) p}
  zero_mem' := ⟨ReducedTensorWords.isGradedCoderivationAlong_zero _ _ _ _,
    LinearMap.isHomogeneous_zero _ _ _⟩
  add_mem' hD hD' := ⟨hD.1.add hD'.1, hD.2.add hD'.2⟩
  smul_mem' r _ hD := ⟨hD.1.smul r, hD.2.smul r⟩

/-- The transformations of a fixed degree form an additive group.  The instance is given
explicitly: instance search does not find `Submodule.addCommGroup` for submodules of linear maps
into reduced tensor words, a direct sum of tensor powers whose two additive structures only agree
after unfolding. -/
instance (p : ℤ) : AddCommGroup (transformationCochains f g p) :=
  @Submodule.addCommGroup R _ _ LinearMap.addCommGroup LinearMap.module _

variable {f g}

/-- Membership in the transformations of degree `p`: being a coderivation along the bar maps with
twist parameter `p`, and having degree `p`. -/
theorem mem_transformationCochains_iff {p : ℤ}
    {D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B} :
    D ∈ transformationCochains f g p ↔
      ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) p f.barMap g.barMap D ∧
        LinearMap.IsHomogeneous D (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
          (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) p :=
  Iff.rfl

namespace transformationCochains

variable {p : ℤ}

/-- A transformation is a coderivation along the bar maps. -/
theorem isGradedCoderivationAlong (D : transformationCochains f g p) :
    ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) p f.barMap g.barMap
      (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  D.2.1

/-- A transformation of degree `p` raises the suspended total degree by `p`. -/
theorem isHomogeneous (D : transformationCochains f g p) :
    LinearMap.IsHomogeneous (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) p :=
  D.2.2

/-- The suspended Taylor components of a transformation: the transformation followed by the
projection onto single letters.  On words of length `n` this is the suspension of the component
`Dₙ`. -/
noncomputable def taylor (D : transformationCochains f g p) : ReducedTensorWords R A →ₗ[R] B :=
  ReducedTensorWords.letter R B ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)

theorem taylor_def (D : transformationCochains f g p) :
    taylor D =
      ReducedTensorWords.letter R B ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  (rfl)

/-- The Taylor components of a transformation of degree `p` have degree `p` for the suspended
gradings. -/
theorem isHomogeneous_taylor (D : transformationCochains f g p) :
    LinearMap.IsHomogeneous (taylor D) (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p := by
  rw [taylor_def]
  simpa only [add_zero] using
    (ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1)).comp (isHomogeneous D)

/-- Transformations of the same degree are determined by their Taylor components. -/
theorem taylor_injective :
    Function.Injective (taylor : transformationCochains f g p → _) := fun D D' e ↦
  Subtype.ext <| (isGradedCoderivationAlong D).eq_of_letter_comp_eq
    (isGradedCoderivationAlong D') e

/-- Two transformations of the same degree with the same Taylor components are equal. -/
@[ext]
theorem ext {D D' : transformationCochains f g p} (e : taylor D = taylor D') : D = D' :=
  taylor_injective e

end transformationCochains

/-! ### The differential -/

/-- The graded commutator `b_B ∘ D - (-1)^p D ∘ b_A` of a transformation of degree `p` with the bar
differentials is a transformation of degree `p + 1`. -/
theorem sub_negOnePow_smul_mem_transformationCochains {p : ℤ}
    {D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B}
    (hD : D ∈ transformationCochains f g p) :
    BB.barDifferential ∘ₗ D - p.negOnePow • (D ∘ₗ AA.barDifferential) ∈
      transformationCochains f g (p + 1) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R]
  refine ⟨hD.1.comp_sub_negOnePow_smul_comp hD.2 AA.isGradedCoderivation_barDifferential
    AA.isHomogeneous_barDifferential BB.isGradedCoderivation_barDifferential
    f.isHomogeneous_barMap f.barDifferential_comp_barMap g.barDifferential_comp_barMap, ?_⟩
  have h₁ : LinearMap.IsHomogeneous (BB.barDifferential ∘ₗ D)
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (p + 1) :=
    BB.isHomogeneous_barDifferential.comp hD.2
  have h₂ : LinearMap.IsHomogeneous (D ∘ₗ AA.barDifferential)
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (p + 1) := by
    rw [add_comm p 1]
    exact hD.2.comp AA.isHomogeneous_barDifferential
  exact h₁.sub (h₂.smul _)

variable (f g) in
/-- The differential of the complex of transformations: a transformation `D` of degree `p` is sent
to its graded commutator `b_B ∘ D - (-1)^p D ∘ b_A` with the bar differentials. -/
noncomputable def transformationDifferential (p : ℤ) :
    transformationCochains f g p →ₗ[R] transformationCochains f g (p + 1) where
  toFun D := ⟨_, sub_negOnePow_smul_mem_transformationCochains D.2⟩
  map_add' D D' := by
    apply Subtype.ext
    simp only [Submodule.coe_add, LinearMap.comp_add, LinearMap.add_comp, smul_add]
    abel
  map_smul' r D := by
    apply Subtype.ext
    refine LinearMap.ext fun z ↦ ?_
    simp only [SetLike.val_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      RingHom.id_apply, map_smul]
    rw [smul_sub, smul_comm r p.negOnePow]

/-- The differential of a transformation is its graded commutator with the bar differentials. -/
@[simp]
theorem coe_transformationDifferential (p : ℤ) (D : transformationCochains f g p) :
    (transformationDifferential f g p D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      BB.barDifferential ∘ₗ D - p.negOnePow • ((D : _ →ₗ[R] _) ∘ₗ AA.barDifferential) :=
  (rfl)

/-- The differential of the complex of transformations squares to zero. -/
@[simp]
theorem transformationDifferential_transformationDifferential (p : ℤ)
    (D : transformationCochains f g p) :
    transformationDifferential f g (p + 1) (transformationDifferential f g p D) = 0 := by
  have hB : BB.barDifferential ∘ₗ BB.barDifferential ∘ₗ
      (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = 0 := by
    rw [← LinearMap.comp_assoc, BB.barDifferential_sq, LinearMap.zero_comp]
  apply Subtype.ext
  simp only [coe_transformationDifferential, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_assoc, AA.barDifferential_sq, hB,
    LinearMap.comp_zero, smul_zero, Int.negOnePow_succ, Units.neg_smul, ZeroMemClass.coe_zero]
  abel_nf

/-- The differential of the complex of transformations composed with itself is zero. -/
theorem transformationDifferential_comp_transformationDifferential (p : ℤ) :
    transformationDifferential f g (p + 1) ∘ₗ transformationDifferential f g p = 0 :=
  LinearMap.ext (transformationDifferential_transformationDifferential p)

/-- The Taylor components of the differential of a transformation: the letter component of
`b_B ∘ D - (-1)^p D ∘ b_A` is `taylor_B ∘ D - (-1)^p taylor(D) ∘ b_A`. -/
theorem transformationCochains.taylor_transformationDifferential {p : ℤ}
    (D : transformationCochains f g p) :
    taylor (transformationDifferential f g p D) =
      BB.taylor ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) -
        p.negOnePow • (taylor D ∘ₗ AA.barDifferential) := by
  simp only [transformationCochains.taylor_def, coe_transformationDifferential,
    LinearMap.comp_sub, LinearMap.comp_smul, ← LinearMap.comp_assoc,
    AInfinityAlgebra.letter_comp_barDifferential]

/-- A transformation of degree zero is closed exactly when it intertwines the bar
differentials. -/
theorem transformationDifferential_zero_eq_zero_iff (D : transformationCochains f g 0) :
    transformationDifferential f g 0 D = 0 ↔
      BB.barDifferential ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
        (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ AA.barDifferential := by
  rw [← Subtype.coe_inj, coe_transformationDifferential, ZeroMemClass.coe_zero,
    Int.negOnePow_zero, one_smul]
  exact ⟨fun h ↦ LinearMap.ext fun z ↦ sub_eq_zero.1 (LinearMap.congr_fun h z),
    fun h ↦ LinearMap.ext fun z ↦ by
      rw [LinearMap.sub_apply, LinearMap.congr_fun h z, sub_self, LinearMap.zero_apply]⟩

/-- For a transformation of degree `-1`, the differential is `b_B ∘ H + H ∘ b_A`. -/
theorem coe_transformationDifferential_neg_one (H : transformationCochains f g (-1)) :
    (transformationDifferential f g (-1) H : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      BB.barDifferential ∘ₗ H +
        (H : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ AA.barDifferential := by
  rw [coe_transformationDifferential, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul,
    one_smul, sub_neg_eq_add]

/-! ### The complex of transformations -/

variable (f g)

/-- The complex of transformations from the `A∞` morphism `f` to the `A∞` morphism `g`.  Its
degree-`p` term is the module of transformations of degree `p`, and its differential is the graded
commutator with the bar differentials. -/
@[expose]
noncomputable def transformationComplex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (transformationCochains f g p))
    (fun p ↦ ModuleCat.ofHom (transformationDifferential f g p))
    (fun p ↦ ModuleCat.hom_ext (transformationDifferential_comp_transformationDifferential p))

/-- The degree-`p` term of the complex of transformations is the module of transformations of
degree `p`. -/
@[simp]
theorem transformationComplex_X (p : ℤ) :
    (transformationComplex f g).X p = ModuleCat.of R (transformationCochains f g p) :=
  (rfl)

/-- The differential of the complex of transformations is induced by
`transformationDifferential`. -/
@[simp]
theorem transformationComplex_d (p : ℤ) :
    (transformationComplex f g).d p (p + 1) =
      ModuleCat.ofHom (transformationDifferential f g p) := by
  apply CochainComplex.of_d

/-! ### Morphisms and homotopies -/

/-- The difference of the bar maps of two `A∞` morphisms is a transformation of degree zero
between them. -/
theorem barMap_sub_barMap_mem_transformationCochains :
    f.barMap - g.barMap ∈ transformationCochains f g 0 :=
  ⟨f.isCoalgHom_barMap.isGradedCoderivationAlong_sub g.isCoalgHom_barMap,
    f.isHomogeneous_barMap.sub g.isHomogeneous_barMap⟩

/-- The difference of the bar maps of two `A∞` morphisms is a closed transformation of degree
zero. -/
@[simp]
theorem transformationDifferential_barMap_sub_barMap :
    transformationDifferential f g 0 ⟨f.barMap - g.barMap,
      barMap_sub_barMap_mem_transformationCochains f g⟩ = 0 := by
  rw [transformationDifferential_zero_eq_zero_iff, LinearMap.comp_sub, LinearMap.sub_comp,
    f.barDifferential_comp_barMap, g.barDifferential_comp_barMap]

namespace Homotopy

variable {f g}

/-- The bar homotopy of a homotopy from `f` to `g` is a transformation of degree `-1`. -/
theorem barHomotopy_mem_transformationCochains (h : Homotopy f g) :
    h.barHomotopy ∈ transformationCochains f g (-1) :=
  ⟨ReducedTensorWords.isGradedCoderivationAlong_neg_iff.2 h.isGradedCoderivationAlong_barHomotopy,
    h.isHomogeneous_barHomotopy⟩

/-- Homotopies from `f` to `g` are exactly the transformations of degree `-1` whose differential
is the difference of the bar maps of `f` and `g`. -/
def equivCochains :
    Homotopy f g ≃ {H : transformationCochains f g (-1) //
      (transformationDifferential f g (-1) H :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = f.barMap - g.barMap} where
  toFun h := ⟨⟨h.barHomotopy, h.barHomotopy_mem_transformationCochains⟩, by
    rw [coe_transformationDifferential_neg_one]
    exact h.barMap_sub_barMap.symm⟩
  invFun H :=
    { barHomotopy := H.1
      isGradedCoderivationAlong_barHomotopy :=
        ReducedTensorWords.isGradedCoderivationAlong_neg_iff.1
          (transformationCochains.isGradedCoderivationAlong H.1)
      isHomogeneous_barHomotopy := transformationCochains.isHomogeneous H.1
      barMap_sub_barMap := H.2.symm.trans (coe_transformationDifferential_neg_one H.1) }
  left_inv _ := (rfl)
  right_inv _ := (rfl)

/-- The transformation of a homotopy is its bar homotopy. -/
@[simp]
theorem coe_equivCochains (h : Homotopy f g) :
    ((equivCochains h : transformationCochains f g (-1)) :
      ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = h.barHomotopy :=
  (rfl)

/-- The homotopy of a bounding transformation has that transformation as its bar homotopy. -/
@[simp]
theorem barHomotopy_equivCochains_symm (H : {H : transformationCochains f g (-1) //
      (transformationDifferential f g (-1) H :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = f.barMap - g.barMap}) :
    (equivCochains.symm H).barHomotopy =
      ((H : transformationCochains f g (-1)) :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  (rfl)

end Homotopy

/-! ### Composition with morphisms -/

namespace transformationCochains

variable {f g} {p : ℤ}

/-- A transformation from `f` to `g` followed by an `A∞` morphism `k`: a transformation of the same
degree from `k ∘ f` to `k ∘ g`. -/
def compRight (k : AInfinityHom BB CC) (p : ℤ) :
    transformationCochains f g p →ₗ[R] transformationCochains (k.comp f) (k.comp g) p where
  toFun D := ⟨k.barMap ∘ₗ D, by
    refine ⟨?_, ?_⟩
    · simpa only [barMap_comp] using
        k.isCoalgHom_barMap.comp_isGradedCoderivationAlong (isGradedCoderivationAlong D)
    · simpa only [add_zero] using k.isHomogeneous_barMap.comp (isHomogeneous D)⟩
  map_add' _ _ := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' _ _ := Subtype.ext (LinearMap.comp_smul _ _ _)

@[simp]
theorem coe_compRight (k : AInfinityHom BB CC) (D : transformationCochains f g p) :
    (compRight k p D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R C) =
      k.barMap ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  (rfl)

/-- Postcomposition computes the Taylor components using the Taylor map of the morphism. -/
theorem taylor_compRight (k : AInfinityHom BB CC) (D : transformationCochains f g p) :
    taylor (compRight k p D) =
      k.taylor ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) := by
  simp only [taylor_def, coe_compRight, AInfinityHom.taylor_def, LinearMap.comp_assoc]

/-- An `A∞` morphism `k` followed by a transformation from `f` to `g`: a transformation of the same
degree from `f ∘ k` to `g ∘ k`. -/
def compLeft (k : AInfinityHom CC AA) (p : ℤ) :
    transformationCochains f g p →ₗ[R] transformationCochains (f.comp k) (g.comp k) p where
  toFun D := ⟨(D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ k.barMap, by
    refine ⟨?_, ?_⟩
    · simpa only [barMap_comp] using
        (isGradedCoderivationAlong D).comp_isCoalgHom k.isCoalgHom_barMap k.isHomogeneous_barMap
    · simpa only [zero_add] using (isHomogeneous D).comp k.isHomogeneous_barMap⟩
  map_add' _ _ := Subtype.ext (LinearMap.add_comp _ _ _)
  map_smul' _ _ := Subtype.ext (LinearMap.smul_comp _ _ _)

@[simp]
theorem coe_compLeft (k : AInfinityHom CC AA) (D : transformationCochains f g p) :
    (compLeft k p D : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) =
      (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ k.barMap :=
  (rfl)

/-- Precomposition computes the Taylor components using the bar map of the morphism. -/
theorem taylor_compLeft (k : AInfinityHom CC AA) (D : transformationCochains f g p) :
    taylor (compLeft k p D) = taylor D ∘ₗ k.barMap :=
  (rfl)

end transformationCochains

variable {f g}

/-- Composing transformations with a morphism after them commutes with the differential. -/
theorem transformationDifferential_compRight (k : AInfinityHom BB CC) {p : ℤ}
    (D : transformationCochains f g p) :
    transformationDifferential (k.comp f) (k.comp g) p (transformationCochains.compRight k p D) =
      transformationCochains.compRight k (p + 1) (transformationDifferential f g p D) := by
  apply Subtype.ext
  simp only [coe_transformationDifferential, transformationCochains.coe_compRight,
    LinearMap.comp_sub, LinearMap.comp_smul, ← LinearMap.comp_assoc,
    k.barDifferential_comp_barMap]

/-- Composing transformations with a morphism before them commutes with the differential. -/
theorem transformationDifferential_compLeft (k : AInfinityHom CC AA) {p : ℤ}
    (D : transformationCochains f g p) :
    transformationDifferential (f.comp k) (g.comp k) p (transformationCochains.compLeft k p D) =
      transformationCochains.compLeft k (p + 1) (transformationDifferential f g p D) := by
  apply Subtype.ext
  simp only [coe_transformationDifferential, transformationCochains.coe_compLeft,
    LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    k.barDifferential_comp_barMap]

end AInfinityHom

end TauCeti
