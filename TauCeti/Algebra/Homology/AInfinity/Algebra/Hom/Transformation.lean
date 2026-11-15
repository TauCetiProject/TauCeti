/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Basic
public import TauCeti.Algebra.Homology.Contraction.Linear.HomotopyEquiv

/-!
# The complex of reduced transformations between A-infinity morphisms

Let `f g : A ⟶ B` be morphisms of `A∞` algebras, with bar maps `F` and `G` between the reduced bar
constructions `Tᶜ(sA)` and `Tᶜ(sB)`.  Following Lyubashenko, a *transformation* of degree `p` from
`f` to `g` is an `(F, G)`-coderivation of degree `p` between the coaugmented bar constructions,
whose Taylor components `rₙ : A^{⊗ n} ⟶ B` have degree `p - n + 1` and include a nullary
component `r₀`, an element of `B` of degree `p + 1`.  This file treats only the *reduced*
transformations, those with `r₀ = 0`.  They are exactly the `(F, G)`-coderivations between the
reduced bar constructions: linear maps `D : Tᶜ(sA) ⟶ Tᶜ(sB)` raising the suspended total degree by
`p` and satisfying

`Δ ∘ D = (D ⊗ G) ∘ Δ + (F ⊗ D) ∘ (τ ⊗ 1) ∘ Δ`,

with `τ` the letterwise Koszul twist of parameter `p` of `Tᶜ(sA)`.  Such a map is determined by its
suspended Taylor components `π ∘ D`, the components `Dₙ` for `n ≥ 1`, and conversely every
homogeneous Taylor map `Tᶜ(sA) ⟶ sB` of degree `p` reconstructs a unique reduced transformation
(`reducedTransformationCochains.ofTaylor`).  A sequence of reduced transformations whose Taylor
components stabilise along the conilpotence filtration converges to a reduced transformation
(`reducedTransformationCochains.limit`).

The differential of a reduced transformation is its graded commutator with the bar differentials,

`δD = b_B ∘ D - (-1)^p D ∘ b_A`,

which is again a reduced transformation, of degree `p + 1`, because `F` and `G` intertwine the bar
differentials; `δ² = 0` because `b_A² = 0` and `b_B² = 0`.  These reduced transformations and their
differential form the cochain complex of `R`-modules
`AInfinityHom.reducedTransformationComplex f g`.  Since the `A∞` structures are uncurved and the
morphisms have no nullary components, the nullary component of the differential of a
transformation only involves `r₀`, so the reduced transformations form a subcomplex of the
one-object case of Lyubashenko's complex of `A∞` transformations between `A∞` functors.  The full
complex, with nullary components, and the composition of transformations, which makes the `A∞`
category of `A∞` functors, are not constructed here.  The sign of the differential is that of the
morphism complexes of right `A∞` modules, `TauCeti.AInfinityRightModule.homDifferential`.

The existing notions sit inside this complex.  The difference `F - G` of the bar maps is a closed
reduced transformation of degree zero, and a homotopy from `f` to `g` in the sense of Keller,
which has no nullary component, is exactly a reduced transformation of degree `-1` whose
differential is `F - G`; so `f` and `g` are homotopic exactly when `F - G` is a coboundary in this
complex.  Composing with an `A∞` morphism on either side maps reduced transformations to reduced
transformations and commutes with the differential, extending the composition of homotopies with
morphisms.  When the linear part of `f : A ⟶ B` underlies a homogeneous `LinearHomotopyEquiv`,
cocycles in `reducedTransformationCochains k₁ k₂ (p + 1)` that become coboundaries after
postcomposition with `f` lift to coboundaries before `f`
(`AInfinityHom.exists_reducedTransformationDifferential_eq_of_compRight`).

## Main definitions

* `TauCeti.AInfinityHom.reducedTransformationCochains`: the reduced transformations of degree `p`
  from `f` to `g`, the `(F, G)`-coderivations of degree `p` between reduced bar constructions.
* `TauCeti.AInfinityHom.reducedTransformationCochains.taylor`, `ofTaylor`, and `limit`: suspended
  Taylor components, reconstruction from Taylor components, and filtration limits.
* `TauCeti.AInfinityHom.reducedTransformationDifferential`: the graded commutator with the bar
  differentials.
* `TauCeti.AInfinityHom.reducedTransformationComplex`: the complex of reduced transformations from
  `f` to `g`.
* `TauCeti.AInfinityHom.reducedTransformationCochains.compRight` and
  `TauCeti.AInfinityHom.reducedTransformationCochains.compLeft`: composition of reduced
  transformations with an `A∞` morphism after or before them.
* `TauCeti.AInfinityHom.Homotopy.equivCochains`: homotopies from `f` to `g` are the reduced
  transformations of degree `-1` bounding `F - G`.

## Main results

* `TauCeti.AInfinityHom.reducedTransformationCochains.ext`: a reduced transformation is determined
  by its Taylor components.
* `TauCeti.AInfinityHom.reducedTransformationDifferential_reducedTransformationDifferential`: the
  differential squares to zero.
* `TauCeti.AInfinityHom.reducedTransformationCochains.taylor_reducedTransformationDifferential`:
  the Taylor components of the differential of a reduced transformation.
* `TauCeti.AInfinityHom.reducedTransformationDifferential_barMap_sub_barMap`: the difference of
  the bar maps is a closed reduced transformation of degree zero.
* `TauCeti.AInfinityHom.reducedTransformationDifferential_compRight` and
  `TauCeti.AInfinityHom.reducedTransformationDifferential_compLeft`: composition with a morphism
  commutes with the differential.
* `TauCeti.AInfinityHom.Homotopy.equivCochains_compRight` and
  `TauCeti.AInfinityHom.Homotopy.equivCochains_compLeft`: the identification of homotopies with
  transformations is compatible with composition with a morphism.
* `TauCeti.AInfinityHom.exists_reducedTransformationDifferential_eq_of_compRight`: lifting closed
  reduced transformations along postcomposition with a linear homotopy equivalence.

## References

* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), Sections 1--2, for `A∞` transformations as coderivations along a pair of `A∞` functors
  and their differential.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7, for homotopies.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Chapitre 1, Lemme 1.3.1.3, for acyclicity of
  postcomposition on reduced transformations.
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

/-- The reduced transformations of degree `p` from the `A∞` morphism `f` to the `A∞` morphism
`g`, the transformations with vanishing nullary component: the linear maps of reduced bar
constructions of degree `p` for the suspended gradings which are coderivations along the bar maps
of `f` and `g` with twist parameter `p`. -/
def reducedTransformationCochains (p : ℤ) :
    Submodule R (ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) where
  carrier := {D |
    ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) p f.barMap g.barMap D ∧
      LinearMap.IsHomogeneous D (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
        (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) p}
  zero_mem' := ⟨ReducedTensorWords.isGradedCoderivationAlong_zero _ _ _ _,
    LinearMap.isHomogeneous_zero _ _ _⟩
  add_mem' hD hD' := ⟨hD.1.add hD'.1, hD.2.add hD'.2⟩
  smul_mem' r _ hD := ⟨hD.1.smul r, hD.2.smul r⟩

/-- The reduced transformations of a fixed degree form an additive group.  The instance is given
explicitly: instance search does not find `Submodule.addCommGroup` for submodules of linear maps
into reduced tensor words, a direct sum of tensor powers whose two additive structures only agree
after unfolding. -/
instance (p : ℤ) : AddCommGroup (reducedTransformationCochains f g p) :=
  @Submodule.addCommGroup R _ _ LinearMap.addCommGroup LinearMap.module _

variable {f g}

/-- Membership in the transformations of degree `p`: being a coderivation along the bar maps with
twist parameter `p`, and having degree `p`. -/
theorem mem_reducedTransformationCochains_iff {p : ℤ}
    {D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B} :
    D ∈ reducedTransformationCochains f g p ↔
      ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) p f.barMap g.barMap D ∧
        LinearMap.IsHomogeneous D (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
          (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) p :=
  Iff.rfl

namespace reducedTransformationCochains

variable {p : ℤ}

/-- A transformation is a coderivation along the bar maps. -/
theorem isGradedCoderivationAlong (D : reducedTransformationCochains f g p) :
    ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) p f.barMap g.barMap
      (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  D.2.1

/-- A transformation of degree `p` raises the suspended total degree by `p`. -/
theorem isHomogeneous (D : reducedTransformationCochains f g p) :
    LinearMap.IsHomogeneous (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) p :=
  D.2.2

/-- The suspended Taylor components of a transformation: the transformation followed by the
projection onto single letters.  On words of length `n` this is the suspension of the component
`Dₙ`. -/
noncomputable def taylor (D : reducedTransformationCochains f g p) :
    ReducedTensorWords R A →ₗ[R] B :=
  ReducedTensorWords.letter R B ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)

theorem taylor_def (D : reducedTransformationCochains f g p) :
    taylor D =
      ReducedTensorWords.letter R B ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  (rfl)

theorem taylor_apply (D : reducedTransformationCochains f g p) (z : ReducedTensorWords R A) :
    taylor D z =
      ReducedTensorWords.letter R B
        ((D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z) :=
  (rfl)

/-- The zero transformation has zero Taylor components. -/
@[simp]
theorem taylor_zero : taylor (0 : reducedTransformationCochains f g p) = 0 :=
  LinearMap.comp_zero _

/-- The Taylor components of a sum of transformations are the sums of their Taylor
components. -/
@[simp]
theorem taylor_add (D D' : reducedTransformationCochains f g p) :
    taylor (D + D') = taylor D + taylor D' :=
  LinearMap.comp_add _ _ _

@[simp]
theorem coe_neg (D : reducedTransformationCochains f g p) :
    ((-D : reducedTransformationCochains f g p) :
      ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = -D :=
  (rfl)

@[simp]
theorem coe_sub (D D' : reducedTransformationCochains f g p) :
    ((D - D' : reducedTransformationCochains f g p) :
      ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = D - D' :=
  (rfl)

/-- The Taylor components of the negation of a transformation are the negations of its Taylor
components. -/
@[simp]
theorem taylor_neg (D : reducedTransformationCochains f g p) :
    taylor (-D) = -taylor D :=
  LinearMap.comp_neg _ _

/-- The Taylor components of a difference of transformations are the differences of their Taylor
components. -/
@[simp]
theorem taylor_sub (D D' : reducedTransformationCochains f g p) :
    taylor (D - D') = taylor D - taylor D' :=
  LinearMap.comp_sub _ _ _

/-- The Taylor components of a scalar multiple of a transformation are the scalar multiples of
its Taylor components. -/
@[simp]
theorem taylor_smul (r : R) (D : reducedTransformationCochains f g p) :
    taylor (r • D) = r • taylor D :=
  LinearMap.comp_smul _ _ _

/-- The Taylor components of a transformation of degree `p` have degree `p` for the suspended
gradings. -/
theorem isHomogeneous_taylor (D : reducedTransformationCochains f g p) :
    LinearMap.IsHomogeneous (taylor D) (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p := by
  rw [taylor_def]
  simpa only [add_zero] using
    (ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1)).comp (isHomogeneous D)

/-- Transformations of the same degree are determined by their Taylor components. -/
theorem taylor_injective :
    Function.Injective (taylor : reducedTransformationCochains f g p → _) := fun D D' e ↦
  Subtype.ext <| (isGradedCoderivationAlong D).eq_of_letter_comp_eq
    (isGradedCoderivationAlong D') e

/-- Two transformations of the same degree with the same Taylor components are equal. -/
@[ext]
theorem ext {D D' : reducedTransformationCochains f g p} (e : taylor D = taylor D') : D = D' :=
  taylor_injective e

variable (f g) in
/-- Reconstruct a reduced transformation of degree `p` from `f` to `g` from its suspended Taylor
components. -/
noncomputable def ofTaylor (t : ReducedTensorWords R A →ₗ[R] B)
    (ht : LinearMap.IsHomogeneous t (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p) :
    reducedTransformationCochains f g p :=
  ⟨ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) p f.barMap g.barMap t,
    ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong f.isCoalgHom_barMap
      g.isCoalgHom_barMap t,
    ReducedTensorWords.isHomogeneous_gradedCoderivAlong f.isHomogeneous_barMap
      g.isHomogeneous_barMap ht⟩

@[simp]
theorem coe_ofTaylor (t : ReducedTensorWords R A →ₗ[R] B)
    (ht : LinearMap.IsHomogeneous t (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p) :
    (ofTaylor f g t ht : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) p f.barMap g.barMap t :=
  (rfl)

@[simp]
theorem taylor_ofTaylor (t : ReducedTensorWords R A →ₗ[R] B)
    (ht : LinearMap.IsHomogeneous t (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p) :
    taylor (ofTaylor f g t ht) = t :=
  ReducedTensorWords.letter_comp_gradedCoderivAlong _ _ _ _ _

@[simp]
theorem ofTaylor_taylor (D : reducedTransformationCochains f g p) :
    ofTaylor f g (taylor D) (isHomogeneous_taylor D) = D :=
  ext (taylor_ofTaylor _ _)

/-- A reduced transformation preserves the conilpotence filtration. -/
theorem mem_filtration (D : reducedTransformationCochains f g p) {n : ℕ}
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.filtration R A n) :
    (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z ∈
      ReducedTensorWords.filtration R B n := by
  rw [← ofTaylor_taylor D, coe_ofTaylor]
  exact ReducedTensorWords.gradedCoderivAlong_mem_filtration g.isCoalgHom_barMap (taylor D) hz

/-- The limit of a sequence of reduced transformations whose Taylor components stabilise along the
conilpotence filtration. -/
noncomputable def limit (D : ℕ → reducedTransformationCochains f g p)
    (hD : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R A n, taylor (D (n + 1)) z = taylor (D n) z) :
    reducedTransformationCochains f g p :=
  ofTaylor f g (ReducedTensorWords.stabilisingLimit fun n ↦ taylor (D n))
    (ReducedTensorWords.isHomogeneous_stabilisingLimit hD fun n ↦ isHomogeneous_taylor (D n))

/-- On the words of length at most `n`, the Taylor components of `limit D hD` agree with those of
`D n`. -/
theorem taylor_limit_apply_of_mem_filtration {D : ℕ → reducedTransformationCochains f g p}
    (hD : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R A n, taylor (D (n + 1)) z = taylor (D n) z)
    {n : ℕ} {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.filtration R A n) :
    taylor (limit D hD) z = taylor (D n) z := by
  rw [limit, taylor_ofTaylor, ReducedTensorWords.stabilisingLimit_apply_of_mem_filtration hD hz]

/-- On the words of length at most `n`, `limit D hD` agrees with `D n`. -/
theorem coe_limit_apply_of_mem_filtration {D : ℕ → reducedTransformationCochains f g p}
    (hD : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R A n, taylor (D (n + 1)) z = taylor (D n) z)
    {n : ℕ} {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.filtration R A n) :
    (limit D hD : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z =
      (D n : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z :=
  (isGradedCoderivationAlong (limit D hD)).apply_eq_of_mem_filtration
    (isGradedCoderivationAlong (D n))
    (fun _ hw ↦ taylor_limit_apply_of_mem_filtration hD hw) hz

end reducedTransformationCochains

/-! ### The differential -/

/-- The graded commutator `b_B ∘ D - (-1)^p D ∘ b_A` of a transformation of degree `p` with the bar
differentials is a transformation of degree `p + 1`. -/
theorem sub_negOnePow_smul_mem_reducedTransformationCochains {p : ℤ}
    {D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B}
    (hD : D ∈ reducedTransformationCochains f g p) :
    BB.barDifferential ∘ₗ D - p.negOnePow • (D ∘ₗ AA.barDifferential) ∈
      reducedTransformationCochains f g (p + 1) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R]
  have hδ := hD.1.comp_sub_negOnePow_smul_comp hD.2 AA.isGradedCoderivation_barDifferential
    AA.isHomogeneous_barDifferential (by rw [mul_one, one_mul])
    BB.isGradedCoderivation_barDifferential f.isHomogeneous_barMap f.barDifferential_comp_barMap
    g.barDifferential_comp_barMap
  rw [one_mul] at hδ
  refine ⟨hδ, ?_⟩
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
/-- The differential of the complex of reduced transformations: a reduced transformation `D` of
degree `p` is sent to its graded commutator `b_B ∘ D - (-1)^p D ∘ b_A` with the bar
differentials. -/
noncomputable def reducedTransformationDifferential (p : ℤ) :
    reducedTransformationCochains f g p →ₗ[R] reducedTransformationCochains f g (p + 1) where
  toFun D := ⟨_, sub_negOnePow_smul_mem_reducedTransformationCochains D.2⟩
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
theorem coe_reducedTransformationDifferential (p : ℤ) (D : reducedTransformationCochains f g p) :
    (reducedTransformationDifferential f g p D :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      BB.barDifferential ∘ₗ D - p.negOnePow • ((D : _ →ₗ[R] _) ∘ₗ AA.barDifferential) :=
  (rfl)

/-- The differential of the complex of transformations squares to zero. -/
@[simp]
theorem reducedTransformationDifferential_reducedTransformationDifferential (p : ℤ)
    (D : reducedTransformationCochains f g p) :
    reducedTransformationDifferential f g (p + 1)
      (reducedTransformationDifferential f g p D) = 0 := by
  have hB : BB.barDifferential ∘ₗ BB.barDifferential ∘ₗ
      (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = 0 := by
    rw [← LinearMap.comp_assoc, BB.barDifferential_sq, LinearMap.zero_comp]
  apply Subtype.ext
  simp only [coe_reducedTransformationDifferential, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_assoc, AA.barDifferential_sq, hB,
    LinearMap.comp_zero, smul_zero, Int.negOnePow_succ, Units.neg_smul, ZeroMemClass.coe_zero]
  abel_nf

/-- The differential of the complex of transformations composed with itself is zero. -/
theorem reducedTransformationDifferential_comp_reducedTransformationDifferential (p : ℤ) :
    reducedTransformationDifferential f g (p + 1) ∘ₗ reducedTransformationDifferential f g p = 0 :=
  LinearMap.ext (reducedTransformationDifferential_reducedTransformationDifferential p)

/-- The Taylor components of the differential of a transformation: the letter component of
`b_B ∘ D - (-1)^p D ∘ b_A` is `taylor_B ∘ D - (-1)^p taylor(D) ∘ b_A`. -/
theorem reducedTransformationCochains.taylor_reducedTransformationDifferential {p : ℤ}
    (D : reducedTransformationCochains f g p) :
    taylor (reducedTransformationDifferential f g p D) =
      BB.taylor ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) -
        p.negOnePow • (taylor D ∘ₗ AA.barDifferential) := by
  simp only [reducedTransformationCochains.taylor_def, coe_reducedTransformationDifferential,
    LinearMap.comp_sub, LinearMap.comp_smul, ← LinearMap.comp_assoc,
    AInfinityAlgebra.letter_comp_barDifferential]

/-- A transformation of degree zero is closed exactly when it intertwines the bar
differentials. -/
theorem reducedTransformationDifferential_zero_eq_zero_iff
    (D : reducedTransformationCochains f g 0) :
    reducedTransformationDifferential f g 0 D = 0 ↔
      BB.barDifferential ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
        (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ AA.barDifferential := by
  rw [← Subtype.coe_inj, coe_reducedTransformationDifferential, ZeroMemClass.coe_zero,
    Int.negOnePow_zero, one_smul]
  exact ⟨fun h ↦ LinearMap.ext fun z ↦ sub_eq_zero.1 (LinearMap.congr_fun h z),
    fun h ↦ LinearMap.ext fun z ↦ by
      rw [LinearMap.sub_apply, LinearMap.congr_fun h z, sub_self, LinearMap.zero_apply]⟩

/-- For a transformation of degree `-1`, the differential is `b_B ∘ H + H ∘ b_A`. -/
theorem coe_reducedTransformationDifferential_neg_one (H : reducedTransformationCochains f g (-1)) :
    (reducedTransformationDifferential f g (-1) H :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      BB.barDifferential ∘ₗ H +
        (H : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ AA.barDifferential := by
  rw [coe_reducedTransformationDifferential, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul,
    one_smul, sub_neg_eq_add]

/-! ### The complex of transformations -/

variable (f g)

/-- The complex of reduced transformations from the `A∞` morphism `f` to the `A∞` morphism `g`,
the subcomplex of transformations with vanishing nullary component.  Its degree-`p` term is the
module of reduced transformations of degree `p`, and its differential is the graded commutator
with the bar differentials. -/
@[expose]
noncomputable def reducedTransformationComplex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (reducedTransformationCochains f g p))
    (fun p ↦ ModuleCat.ofHom (reducedTransformationDifferential f g p))
    (fun p ↦ ModuleCat.hom_ext
      (reducedTransformationDifferential_comp_reducedTransformationDifferential p))

/-- The degree-`p` term of the complex of transformations is the module of transformations of
degree `p`. -/
@[simp]
theorem reducedTransformationComplex_X (p : ℤ) :
    (reducedTransformationComplex f g).X p = ModuleCat.of R (reducedTransformationCochains f g p) :=
  (rfl)

/-- The differential of the complex of transformations is induced by
`reducedTransformationDifferential`. -/
@[simp]
theorem reducedTransformationComplex_d (p : ℤ) :
    (reducedTransformationComplex f g).d p (p + 1) =
      ModuleCat.ofHom (reducedTransformationDifferential f g p) := by
  apply CochainComplex.of_d

/-! ### Morphisms and homotopies -/

/-- The difference of the bar maps of two `A∞` morphisms is a transformation of degree zero
between them. -/
theorem barMap_sub_barMap_mem_reducedTransformationCochains :
    f.barMap - g.barMap ∈ reducedTransformationCochains f g 0 :=
  ⟨f.isCoalgHom_barMap.isGradedCoderivationAlong_sub g.isCoalgHom_barMap,
    f.isHomogeneous_barMap.sub g.isHomogeneous_barMap⟩

/-- The difference of the bar maps of two `A∞` morphisms is a closed transformation of degree
zero. -/
@[simp]
theorem reducedTransformationDifferential_barMap_sub_barMap :
    reducedTransformationDifferential f g 0 ⟨f.barMap - g.barMap,
      barMap_sub_barMap_mem_reducedTransformationCochains f g⟩ = 0 := by
  rw [reducedTransformationDifferential_zero_eq_zero_iff, LinearMap.comp_sub, LinearMap.sub_comp,
    f.barDifferential_comp_barMap, g.barDifferential_comp_barMap]

namespace Homotopy

variable {f g}

/-- The bar homotopy of a homotopy from `f` to `g` is a transformation of degree `-1`. -/
theorem barHomotopy_mem_reducedTransformationCochains (h : Homotopy f g) :
    h.barHomotopy ∈ reducedTransformationCochains f g (-1) :=
  ⟨ReducedTensorWords.isGradedCoderivationAlong_neg_iff.2 h.isGradedCoderivationAlong_barHomotopy,
    h.isHomogeneous_barHomotopy⟩

/-- Homotopies from `f` to `g` are exactly the reduced transformations of degree `-1` whose
differential is the difference of the bar maps of `f` and `g`. -/
def equivCochains :
    Homotopy f g ≃ {H : reducedTransformationCochains f g (-1) //
      (reducedTransformationDifferential f g (-1) H :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = f.barMap - g.barMap} where
  toFun h := ⟨⟨h.barHomotopy, h.barHomotopy_mem_reducedTransformationCochains⟩, by
    rw [coe_reducedTransformationDifferential_neg_one]
    exact h.barMap_sub_barMap.symm⟩
  invFun H :=
    { barHomotopy := H.1
      isGradedCoderivationAlong_barHomotopy :=
        ReducedTensorWords.isGradedCoderivationAlong_neg_iff.1
          (reducedTransformationCochains.isGradedCoderivationAlong H.1)
      isHomogeneous_barHomotopy := reducedTransformationCochains.isHomogeneous H.1
      barMap_sub_barMap := H.2.symm.trans (coe_reducedTransformationDifferential_neg_one H.1) }
  left_inv _ := (rfl)
  right_inv _ := (rfl)

/-- The transformation of a homotopy is its bar homotopy. -/
@[simp]
theorem coe_equivCochains (h : Homotopy f g) :
    ((equivCochains h : reducedTransformationCochains f g (-1)) :
      ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = h.barHomotopy :=
  (rfl)

/-- The homotopy of a bounding transformation has that transformation as its bar homotopy. -/
@[simp]
theorem barHomotopy_equivCochains_symm (H : {H : reducedTransformationCochains f g (-1) //
      (reducedTransformationDifferential f g (-1) H :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = f.barMap - g.barMap}) :
    (equivCochains.symm H).barHomotopy =
      ((H : reducedTransformationCochains f g (-1)) :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  (rfl)

end Homotopy

/-! ### Composition with morphisms -/

namespace reducedTransformationCochains

variable {f g} {p : ℤ}

/-- A transformation from `f` to `g` followed by an `A∞` morphism `k`: a transformation of the same
degree from `k ∘ f` to `k ∘ g`. -/
def compRight (k : AInfinityHom BB CC) (p : ℤ) :
    reducedTransformationCochains f g p →ₗ[R]
      reducedTransformationCochains (k.comp f) (k.comp g) p where
  toFun D := ⟨k.barMap ∘ₗ D, by
    refine ⟨?_, ?_⟩
    · simpa only [barMap_comp] using
        k.isCoalgHom_barMap.comp_isGradedCoderivationAlong (isGradedCoderivationAlong D)
    · simpa only [add_zero] using k.isHomogeneous_barMap.comp (isHomogeneous D)⟩
  map_add' _ _ := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' _ _ := Subtype.ext (LinearMap.comp_smul _ _ _)

@[simp]
theorem coe_compRight (k : AInfinityHom BB CC) (D : reducedTransformationCochains f g p) :
    (compRight k p D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R C) =
      k.barMap ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) :=
  (rfl)

/-- Postcomposition computes the Taylor components using the Taylor map of the morphism. -/
theorem taylor_compRight (k : AInfinityHom BB CC) (D : reducedTransformationCochains f g p) :
    taylor (compRight k p D) =
      k.taylor ∘ₗ (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) := by
  simp only [taylor_def, coe_compRight, AInfinityHom.taylor_def, LinearMap.comp_assoc]

/-- An `A∞` morphism `k` followed by a transformation from `f` to `g`: a transformation of the same
degree from `f ∘ k` to `g ∘ k`. -/
def compLeft (k : AInfinityHom CC AA) (p : ℤ) :
    reducedTransformationCochains f g p →ₗ[R]
      reducedTransformationCochains (f.comp k) (g.comp k) p where
  toFun D := ⟨(D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ k.barMap, by
    refine ⟨?_, ?_⟩
    · simpa only [barMap_comp] using
        (isGradedCoderivationAlong D).comp_isCoalgHom k.isCoalgHom_barMap k.isHomogeneous_barMap
    · simpa only [zero_add] using (isHomogeneous D).comp k.isHomogeneous_barMap⟩
  map_add' _ _ := Subtype.ext (LinearMap.add_comp _ _ _)
  map_smul' _ _ := Subtype.ext (LinearMap.smul_comp _ _ _)

@[simp]
theorem coe_compLeft (k : AInfinityHom CC AA) (D : reducedTransformationCochains f g p) :
    (compLeft k p D : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) =
      (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) ∘ₗ k.barMap :=
  (rfl)

/-- Precomposition computes the Taylor components using the bar map of the morphism. -/
theorem taylor_compLeft (k : AInfinityHom CC AA) (D : reducedTransformationCochains f g p) :
    taylor (compLeft k p D) = taylor D ∘ₗ k.barMap :=
  (rfl)

end reducedTransformationCochains

variable {f g}

/-- Composing transformations with a morphism after them commutes with the differential. -/
theorem reducedTransformationDifferential_compRight (k : AInfinityHom BB CC) {p : ℤ}
    (D : reducedTransformationCochains f g p) :
    reducedTransformationDifferential (k.comp f) (k.comp g) p
        (reducedTransformationCochains.compRight k p D) =
      reducedTransformationCochains.compRight k (p + 1)
        (reducedTransformationDifferential f g p D) := by
  apply Subtype.ext
  simp only [coe_reducedTransformationDifferential, reducedTransformationCochains.coe_compRight,
    LinearMap.comp_sub, LinearMap.comp_smul, ← LinearMap.comp_assoc,
    k.barDifferential_comp_barMap]

/-- Composing transformations with a morphism before them commutes with the differential. -/
theorem reducedTransformationDifferential_compLeft (k : AInfinityHom CC AA) {p : ℤ}
    (D : reducedTransformationCochains f g p) :
    reducedTransformationDifferential (f.comp k) (g.comp k) p
        (reducedTransformationCochains.compLeft k p D) =
      reducedTransformationCochains.compLeft k (p + 1)
        (reducedTransformationDifferential f g p D) := by
  apply Subtype.ext
  simp only [coe_reducedTransformationDifferential, reducedTransformationCochains.coe_compLeft,
    LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    k.barDifferential_comp_barMap]

namespace Homotopy

/-- The transformation of a homotopy followed by an `A∞` morphism is the transformation of the
homotopy followed by that morphism. -/
@[simp]
theorem equivCochains_compRight (h : Homotopy f g) (k : AInfinityHom BB CC) :
    (equivCochains (h.compRight k) : reducedTransformationCochains (k.comp f) (k.comp g) (-1)) =
      reducedTransformationCochains.compRight k (-1) (equivCochains h) :=
  Subtype.ext (barHomotopy_compRight h k)

/-- The transformation of an `A∞` morphism followed by a homotopy is that morphism followed by
the transformation of the homotopy. -/
@[simp]
theorem equivCochains_compLeft (h : Homotopy f g) (k : AInfinityHom CC AA) :
    (equivCochains (h.compLeft k) : reducedTransformationCochains (f.comp k) (g.comp k) (-1)) =
      reducedTransformationCochains.compLeft k (-1) (equivCochains h) :=
  Subtype.ext (barHomotopy_compLeft h k)

end Homotopy

/-! ### Lifting cocycles along postcomposition -/

section LiftCompRight

/-- Reindex the differential of a reduced transformation of degree `p - 1` into degree `p`,
avoiding the non-definitional arithmetic rewrite `(p - 1) + 1 = p`. -/
private noncomputable def predDifferential {f' g' : AInfinityHom CC BB} (p : ℤ)
    (Z : reducedTransformationCochains f' g' (p - 1)) :
    reducedTransformationCochains f' g' p :=
  ⟨reducedTransformationDifferential f' g' (p - 1) Z, by
    simpa only [sub_add_cancel] using (reducedTransformationDifferential f' g' (p - 1) Z).2⟩

@[simp]
private theorem coe_predDifferential {f' g' : AInfinityHom CC BB} (p : ℤ)
    (Z : reducedTransformationCochains f' g' (p - 1)) :
    (predDifferential p Z : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) =
      reducedTransformationDifferential f' g' (p - 1) Z :=
  (rfl)

private theorem predDifferential_add {f' g' : AInfinityHom CC BB} (p : ℤ)
    (Z Z' : reducedTransformationCochains f' g' (p - 1)) :
    predDifferential p (Z + Z') = predDifferential p Z + predDifferential p Z' := by
  apply Subtype.ext
  rw [coe_predDifferential, map_add]
  rfl

private theorem reducedTransformationDifferential_predDifferential {f' g' : AInfinityHom CC BB}
    (p : ℤ) (Z : reducedTransformationCochains f' g' (p - 1)) :
    reducedTransformationDifferential f' g' p (predDifferential p Z) = 0 := by
  have h := congrArg Subtype.val
    (reducedTransformationDifferential_reducedTransformationDifferential (f := f') (g := g')
      (p - 1) Z)
  apply Subtype.ext
  simpa only [coe_reducedTransformationDifferential, coe_predDifferential, sub_add_cancel,
    ZeroMemClass.coe_zero] using h

private theorem taylor_predDifferential {f' g' : AInfinityHom CC BB} (p : ℤ)
    (Z : reducedTransformationCochains f' g' (p - 1)) :
    reducedTransformationCochains.taylor (predDifferential p Z) =
      BB.taylor ∘ₗ (Z : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) -
        (p - 1).negOnePow • (reducedTransformationCochains.taylor Z ∘ₗ CC.barDifferential) :=
  reducedTransformationCochains.taylor_reducedTransformationDifferential Z

/-- Stage `n` of the recursive lift of a closed transformation `U` along `compRight f`. -/
private structure CoupledLiftStage {k₁ k₂ : AInfinityHom CC AA} {f : AInfinityHom AA BB}
    {p : ℤ} (U : reducedTransformationCochains k₁ k₂ (p + 1))
    (V : reducedTransformationCochains (f.comp k₁) (f.comp k₂) p) (n : ℕ) where
  X : reducedTransformationCochains k₁ k₂ p
  Z : reducedTransformationCochains (f.comp k₁) (f.comp k₂) (p - 1)
  hX : ∀ w ∈ ReducedTensorWords.filtration R C n,
    ((U - reducedTransformationDifferential k₁ k₂ p X :
        reducedTransformationCochains k₁ k₂ (p + 1)) :
      ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) w = 0
  hZ : ∀ w ∈ ReducedTensorWords.filtration R C n,
    ((V - reducedTransformationCochains.compRight f p X - predDifferential p Z :
        reducedTransformationCochains (f.comp k₁) (f.comp k₂) p) :
      ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) w = 0

private noncomputable def coupledLiftStageZero {k₁ k₂ : AInfinityHom CC AA}
    {f : AInfinityHom AA BB} {p : ℤ} (U : reducedTransformationCochains k₁ k₂ (p + 1))
    (V : reducedTransformationCochains (f.comp k₁) (f.comp k₂) p) :
    CoupledLiftStage U V 0 where
  X := 0
  Z := 0
  hX w hw := by
    rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hw
    rw [hw, map_zero]
  hZ w hw := by
    rw [ReducedTensorWords.filtration_zero, Submodule.mem_bot] at hw
    rw [hw, map_zero]

private noncomputable def coupledLiftStageSucc {k₁ k₂ : AInfinityHom CC AA}
    {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1))
    {p : ℤ} {U : reducedTransformationCochains k₁ k₂ (p + 1)}
    (hU : reducedTransformationDifferential k₁ k₂ (p + 1) U = 0)
    {V : reducedTransformationCochains (f.comp k₁) (f.comp k₂) p}
    (hV : reducedTransformationDifferential (f.comp k₁) (f.comp k₂) p V =
      reducedTransformationCochains.compRight f (p + 1) U)
    (n : ℕ) (S : CoupledLiftStage U V n) :
    CoupledLiftStage U V (n + 1) := by
  let U' : reducedTransformationCochains k₁ k₂ (p + 1) :=
    U - reducedTransformationDifferential k₁ k₂ p S.X
  let V' : reducedTransformationCochains (f.comp k₁) (f.comp k₂) p :=
    V - reducedTransformationCochains.compRight f p S.X - predDifferential p S.Z
  let L := ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩
  let u : ReducedTensorWords R C →ₗ[R] A := reducedTransformationCochains.taylor U' ∘ₗ L
  let v : ReducedTensorWords R C →ₗ[R] B := reducedTransformationCochains.taylor V' ∘ₗ L
  have hf_sh : LinearMap.IsHomogeneous e.hom
      (AA.grading.shift 1).piece (BB.grading.shift 1).piece 0 :=
    LinearMap.isHomogeneous_shift_piece_iff.2 (he ▸ f.isHomogeneous_linearPart)
  have hg_sh : LinearMap.IsHomogeneous e.inv
      (BB.grading.shift 1).piece (AA.grading.shift 1).piece 0 :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hinv
  have hhA_sh : LinearMap.IsHomogeneous e.homotopyHom
      (AA.grading.shift 1).piece (AA.grading.shift 1).piece (-1) :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hhA
  have hhB_sh : LinearMap.IsHomogeneous e.homotopyInv
      (BB.grading.shift 1).piece (BB.grading.shift 1).piece (-1) :=
    LinearMap.isHomogeneous_shift_piece_iff.2 hhB
  have hu_hom : LinearMap.IsHomogeneous u
      (ReducedTensorWords.gradedPiece (CC.grading.shift 1)) (AA.grading.shift 1).piece (p + 1) := by
    simpa only [zero_add] using
      (reducedTransformationCochains.isHomogeneous_taylor U').comp
        (ReducedTensorWords.isHomogeneous_lengthProj _ _)
  have hv_hom : LinearMap.IsHomogeneous v
      (ReducedTensorWords.gradedPiece (CC.grading.shift 1)) (BB.grading.shift 1).piece p := by
    simpa only [zero_add] using
      (reducedTransformationCochains.isHomogeneous_taylor V').comp
        (ReducedTensorWords.isHomogeneous_lengthProj _ _)
  let x : ReducedTensorWords R C →ₗ[R] A := e.coupledLift u v
  let z : ReducedTensorWords R C →ₗ[R] B := e.coupledHomotopy u v
  have hx_hom : LinearMap.IsHomogeneous x
      (ReducedTensorWords.gradedPiece (CC.grading.shift 1)) (AA.grading.shift 1).piece p :=
    e.isHomogeneous_coupledLift hg_sh hhA_sh hu_hom hv_hom
  have hz_hom : LinearMap.IsHomogeneous z
      (ReducedTensorWords.gradedPiece (CC.grading.shift 1)) (BB.grading.shift 1).piece (p - 1) :=
    e.isHomogeneous_coupledHomotopy hf_sh hg_sh hhA_sh hhB_sh hu_hom hv_hom
  let ΔX := reducedTransformationCochains.ofTaylor k₁ k₂ x hx_hom
  let ΔZ := reducedTransformationCochains.ofTaylor (f.comp k₁) (f.comp k₂) z hz_hom
  -- Deduce the coupled unary cocycle/coboundary equations for `(u, v)` once for both branches.
  have hs_succ : (p + 1).negOnePow = -p.negOnePow := Int.negOnePow_succ p
  have htU'_zero : ∀ w ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor U' w = 0 := fun w hw ↦ by
    rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply, S.hX w hw, map_zero]
  have htV'_zero : ∀ w ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor V' w = 0 := fun w hw ↦ by
    rw [reducedTransformationCochains.taylor_def, LinearMap.comp_apply, S.hZ w hw, map_zero]
  have hδU' : reducedTransformationDifferential k₁ k₂ (p + 1) U' = 0 := by
    rw [map_sub, hU, reducedTransformationDifferential_reducedTransformationDifferential,
      sub_zero]
  have hδV' : reducedTransformationDifferential (f.comp k₁) (f.comp k₂) p V' =
      reducedTransformationCochains.compRight f (p + 1) U' := by
    rw [map_sub, map_sub, hV, reducedTransformationDifferential_compRight,
      reducedTransformationDifferential_predDifferential, sub_zero, map_sub]
  have hu_eq : AA.differential ∘ₗ u -
      (p + 1).negOnePow • (u ∘ₗ CC.unaryBarDifferential) = 0 := by
    refine LinearMap.ext fun y ↦ ?_
    have hLy := ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ y
    have hprim := (reducedTransformationCochains.isGradedCoderivationAlong U')
      |>.apply_eq_ofLetter_of_mem_filtration_succ S.hX hLy
    have hhigh : CC.higherBarDifferential (L y) ∈ ReducedTensorWords.filtration R C n :=
      CC.higherBarDifferential_filtration n ⟨L y, hLy, rfl⟩
    have hcomm : L (CC.unaryBarDifferential y) = CC.unaryBarDifferential (L y) :=
      LinearMap.congr_fun (CC.lengthProj_comp_unaryBarDifferential ⟨n + 1, n.succ_pos⟩) y
    have hval := LinearMap.congr_fun
      (congrArg reducedTransformationCochains.taylor hδU') (L y)
    rw [reducedTransformationCochains.taylor_reducedTransformationDifferential,
      reducedTransformationCochains.taylor_zero, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.zero_apply, hprim,
      ← reducedTransformationCochains.taylor_apply, AInfinityAlgebra.taylor_ofLetter,
      ← AInfinityAlgebra.differential_apply, CC.barDifferential_eq_unary_add_higher,
      LinearMap.add_apply, map_add, htU'_zero _ hhigh, add_zero] at hval
    dsimp only [u]
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply, hcomm]
    exact hval
  have hv_eq : BB.differential ∘ₗ v +
      (p + 1).negOnePow • (v ∘ₗ CC.unaryBarDifferential) = e.hom ∘ₗ u := by
    refine LinearMap.ext fun y ↦ ?_
    have hLy := ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ y
    have hprimU := (reducedTransformationCochains.isGradedCoderivationAlong U')
      |>.apply_eq_ofLetter_of_mem_filtration_succ S.hX hLy
    have hprimV := (reducedTransformationCochains.isGradedCoderivationAlong V')
      |>.apply_eq_ofLetter_of_mem_filtration_succ S.hZ hLy
    have hhigh : CC.higherBarDifferential (L y) ∈ ReducedTensorWords.filtration R C n :=
      CC.higherBarDifferential_filtration n ⟨L y, hLy, rfl⟩
    have hcomm : L (CC.unaryBarDifferential y) = CC.unaryBarDifferential (L y) :=
      LinearMap.congr_fun (CC.lengthProj_comp_unaryBarDifferential ⟨n + 1, n.succ_pos⟩) y
    have hval := LinearMap.congr_fun
      (congrArg reducedTransformationCochains.taylor hδV') (L y)
    rw [reducedTransformationCochains.taylor_reducedTransformationDifferential,
      reducedTransformationCochains.taylor_compRight, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, hprimV, hprimU,
      ← reducedTransformationCochains.taylor_apply, ← reducedTransformationCochains.taylor_apply,
      AInfinityAlgebra.taylor_ofLetter, ← AInfinityAlgebra.differential_apply,
      ← linearPart_apply, ← he, CC.barDifferential_eq_unary_add_higher, LinearMap.add_apply,
      map_add, htV'_zero _ hhigh, add_zero] at hval
    rw [hs_succ, Units.neg_smul, ← sub_eq_add_neg]
    dsimp only [u, v]
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.comp_apply, hcomm]
    exact hval
  have hx_zero : ∀ w ∈ ReducedTensorWords.filtration R C n, x w = 0 := fun w hw ↦ by
    have hLw : L w = 0 :=
      ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R C n.lt_succ_self hw
    simp only [x, LinearHomotopyEquiv.coupledLift_def, u, v, LinearMap.add_apply,
      LinearMap.comp_apply, hLw, map_zero, add_zero]
  have hΔX_zero : ∀ w ∈ ReducedTensorWords.filtration R C n,
      (ΔX : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A) w = 0 := fun w hw ↦
    (reducedTransformationCochains.isGradedCoderivationAlong ΔX)
      |>.apply_eq_zero_of_mem_filtration
      (fun y hy ↦ by
        rw [← reducedTransformationCochains.taylor_apply,
          reducedTransformationCochains.taylor_ofTaylor]
        exact hx_zero y hy) hw
  refine ⟨S.X + ΔX, S.Z + ΔZ, ?_, ?_⟩
  · have hx_sol := e.dM_comp_coupledLift_add_smul hu_eq hv_eq
    intro w hw
    have heq : U - reducedTransformationDifferential k₁ k₂ p (S.X + ΔX) =
        U' - reducedTransformationDifferential k₁ k₂ p ΔX := by
      dsimp only [U']
      rw [map_add, sub_add_eq_sub_sub]
    rw [heq]
    refine (reducedTransformationCochains.isGradedCoderivationAlong
      (U' - reducedTransformationDifferential k₁ k₂ p ΔX)).apply_eq_zero_of_mem_filtration
      (fun y hy ↦ ?_) hw
    rw [← reducedTransformationCochains.taylor_apply,
      reducedTransformationCochains.taylor_sub,
      reducedTransformationCochains.taylor_reducedTransformationDifferential,
      LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.comp_apply]
    have hprimΔX := (reducedTransformationCochains.isGradedCoderivationAlong ΔX)
      |>.apply_eq_ofLetter_of_mem_filtration_succ hΔX_zero hy
    have hhigh : CC.higherBarDifferential y ∈ ReducedTensorWords.filtration R C n :=
      CC.higherBarDifferential_filtration n ⟨y, hy, rfl⟩
    rw [hprimΔX, ← reducedTransformationCochains.taylor_apply,
      reducedTransformationCochains.taylor_ofTaylor, AInfinityAlgebra.taylor_ofLetter,
      ← AInfinityAlgebra.differential_apply, CC.barDifferential_eq_unary_add_higher,
      LinearMap.add_apply, map_add, hx_zero _ hhigh, add_zero]
    have hx_sol_y := LinearMap.congr_fun hx_sol y
    rw [hs_succ, Units.neg_smul, ← sub_eq_add_neg, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.comp_apply] at hx_sol_y
    -- Fold `e.coupledLift u v` back to `x` and `LinearMap.zero_apply` to `0` so `hx_sol_y`
    -- rewrites the differential term directly.
    change reducedTransformationCochains.taylor U' y -
        (AA.differential (x y) - (p.negOnePow • x (CC.unaryBarDifferential y))) = 0
    rw [hx_sol_y]
    have hproj := ReducedTensorWords.apply_lengthProj_of_mem_filtration R C htU'_zero hy
    simpa only [u, L, LinearMap.comp_apply, sub_eq_zero] using hproj.symm
  · have hs_pred : (p - 1).negOnePow = (p + 1).negOnePow := by
      have h₁ := Int.negOnePow_succ (p - 1)
      rw [sub_add_cancel] at h₁
      rw [hs_succ, h₁, neg_neg]
    have hz_sol := e.sub_hom_comp_coupledLift hu_eq hv_eq
    have hz_zero : ∀ w ∈ ReducedTensorWords.filtration R C n, z w = 0 := fun w hw ↦ by
      have hLw : L w = 0 :=
        ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R C n.lt_succ_self hw
      simp only [z, LinearHomotopyEquiv.coupledHomotopy_def, u, v, LinearMap.sub_apply,
        LinearMap.comp_apply, hLw, map_zero, sub_zero]
    have hΔZ_zero : ∀ w ∈ ReducedTensorWords.filtration R C n,
        (ΔZ : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) w = 0 := fun w hw ↦
      (reducedTransformationCochains.isGradedCoderivationAlong ΔZ)
        |>.apply_eq_zero_of_mem_filtration
        (fun y hy ↦ by
          rw [← reducedTransformationCochains.taylor_apply,
            reducedTransformationCochains.taylor_ofTaylor]
          exact hz_zero y hy) hw
    intro w hw
    have heq : V - reducedTransformationCochains.compRight f p (S.X + ΔX) -
          predDifferential p (S.Z + ΔZ) =
        V' - reducedTransformationCochains.compRight f p ΔX - predDifferential p ΔZ := by
      dsimp only [V']
      rw [map_add, predDifferential_add]
      abel
    rw [heq]
    refine (reducedTransformationCochains.isGradedCoderivationAlong
      (V' - reducedTransformationCochains.compRight f p ΔX - predDifferential p ΔZ))
      |>.apply_eq_zero_of_mem_filtration (fun y hy ↦ ?_) hw
    rw [← reducedTransformationCochains.taylor_apply,
      reducedTransformationCochains.taylor_sub, reducedTransformationCochains.taylor_sub,
      reducedTransformationCochains.taylor_compRight, taylor_predDifferential,
      LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    have hprimΔX := (reducedTransformationCochains.isGradedCoderivationAlong ΔX)
      |>.apply_eq_ofLetter_of_mem_filtration_succ hΔX_zero hy
    have hprimΔZ := (reducedTransformationCochains.isGradedCoderivationAlong ΔZ)
      |>.apply_eq_ofLetter_of_mem_filtration_succ hΔZ_zero hy
    have hhigh : CC.higherBarDifferential y ∈ ReducedTensorWords.filtration R C n :=
      CC.higherBarDifferential_filtration n ⟨y, hy, rfl⟩
    rw [hprimΔX, hprimΔZ, ← reducedTransformationCochains.taylor_apply,
      ← reducedTransformationCochains.taylor_apply, reducedTransformationCochains.taylor_ofTaylor,
      reducedTransformationCochains.taylor_ofTaylor, ← linearPart_apply, ← he,
      AInfinityAlgebra.taylor_ofLetter, ← AInfinityAlgebra.differential_apply,
      CC.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add, hz_zero _ hhigh,
      add_zero, hs_pred]
    have hz_sol_y : v y - e.hom (x y) =
        BB.differential (z y) - (p + 1).negOnePow • z (CC.unaryBarDifferential y) := by
      simpa only [x, z, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] using
        LinearMap.congr_fun hz_sol y
    have hproj := ReducedTensorWords.apply_lengthProj_of_mem_filtration R C htV'_zero hy
    rw [← hz_sol_y]
    dsimp only [v]
    rw [LinearMap.comp_apply, hproj, sub_self]

private theorem taylor_coupledLiftStageSucc_X_eq {k₁ k₂ : AInfinityHom CC AA}
    {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1))
    {p : ℤ} {U : reducedTransformationCochains k₁ k₂ (p + 1)}
    (hU : reducedTransformationDifferential k₁ k₂ (p + 1) U = 0)
    {V : reducedTransformationCochains (f.comp k₁) (f.comp k₂) p}
    (hV : reducedTransformationDifferential (f.comp k₁) (f.comp k₂) p V =
      reducedTransformationCochains.compRight f (p + 1) U)
    (n : ℕ) (S : CoupledLiftStage U V n) {w : ReducedTensorWords R C}
    (hw : w ∈ ReducedTensorWords.filtration R C n) :
    reducedTransformationCochains.taylor
        (coupledLiftStageSucc e he hinv hhA hhB hU hV n S).X w =
      reducedTransformationCochains.taylor S.X w := by
  have hLw : ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩ w = 0 :=
    ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R C n.lt_succ_self hw
  simp only [coupledLiftStageSucc, reducedTransformationCochains.taylor_add,
    reducedTransformationCochains.taylor_ofTaylor, LinearHomotopyEquiv.coupledLift_def,
    LinearMap.add_apply, LinearMap.comp_apply, hLw, map_zero, add_zero]

private theorem taylor_coupledLiftStageSucc_Z_eq {k₁ k₂ : AInfinityHom CC AA}
    {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1))
    {p : ℤ} {U : reducedTransformationCochains k₁ k₂ (p + 1)}
    (hU : reducedTransformationDifferential k₁ k₂ (p + 1) U = 0)
    {V : reducedTransformationCochains (f.comp k₁) (f.comp k₂) p}
    (hV : reducedTransformationDifferential (f.comp k₁) (f.comp k₂) p V =
      reducedTransformationCochains.compRight f (p + 1) U)
    (n : ℕ) (S : CoupledLiftStage U V n) {w : ReducedTensorWords R C}
    (hw : w ∈ ReducedTensorWords.filtration R C n) :
    reducedTransformationCochains.taylor
        (coupledLiftStageSucc e he hinv hhA hhB hU hV n S).Z w =
      reducedTransformationCochains.taylor S.Z w := by
  have hLw : ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩ w = 0 :=
    ReducedTensorWords.lengthProj_apply_eq_zero_of_mem_filtration R C n.lt_succ_self hw
  simp only [coupledLiftStageSucc, reducedTransformationCochains.taylor_add,
    reducedTransformationCochains.taylor_ofTaylor, LinearHomotopyEquiv.coupledHomotopy_def,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, hLw, map_zero, sub_zero,
    add_zero]

/-- **Lifting cocycles along postcomposition by a homotopy equivalence.**  Let `k₁, k₂ : C ⟶ A` and
`f : A ⟶ B` be `A∞` morphisms, and suppose the linear part `f₁` of `f` underlies a homogeneous
linear homotopy equivalence `e` between `(A, m₁)` and `(B, m₁)`.  Whenever `U` is a closed reduced
transformation of degree `p + 1` from `k₁` to `k₂` whose postcomposition `compRight f (p + 1) U` is
bounded by `V` of degree `p`, there exist a reduced transformation `X` of degree `p` bounding `U`
and a reduced transformation `Z` of degree `p - 1` bounding the defect
`V - compRight f p X`. -/
theorem exists_reducedTransformationDifferential_eq_of_compRight
    {k₁ k₂ : AInfinityHom CC AA} {f : AInfinityHom AA BB}
    (e : LinearHomotopyEquiv AA.differential BB.differential) (he : e.hom = f.linearPart)
    (hinv : LinearMap.IsHomogeneous e.inv BB.grading.piece AA.grading.piece 0)
    (hhA : LinearMap.IsHomogeneous e.homotopyHom AA.grading.piece AA.grading.piece (-1))
    (hhB : LinearMap.IsHomogeneous e.homotopyInv BB.grading.piece BB.grading.piece (-1))
    {p : ℤ} {U : reducedTransformationCochains k₁ k₂ (p + 1)}
    (hU : reducedTransformationDifferential k₁ k₂ (p + 1) U = 0)
    {V : reducedTransformationCochains (f.comp k₁) (f.comp k₂) p}
    (hV : reducedTransformationDifferential (f.comp k₁) (f.comp k₂) p V =
      reducedTransformationCochains.compRight f (p + 1) U) :
    ∃ (X : reducedTransformationCochains k₁ k₂ p)
      (Z : reducedTransformationCochains (f.comp k₁) (f.comp k₂) (p - 1)),
        reducedTransformationDifferential k₁ k₂ p X = U ∧
          (reducedTransformationDifferential (f.comp k₁) (f.comp k₂) (p - 1) Z :
              ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) =
            (V - reducedTransformationCochains.compRight f p X :
              ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B) := by
  let stage : ∀ n, CoupledLiftStage U V n :=
    Nat.rec (coupledLiftStageZero U V) fun n S ↦
      coupledLiftStageSucc e he hinv hhA hhB hU hV n S
  let seqX : ℕ → reducedTransformationCochains k₁ k₂ p := fun n ↦ (stage n).X
  let seqZ : ℕ → reducedTransformationCochains (f.comp k₁) (f.comp k₂) (p - 1) :=
    fun n ↦ (stage n).Z
  have hstabX : ∀ n, ∀ w ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (seqX (n + 1)) w =
        reducedTransformationCochains.taylor (seqX n) w :=
    fun n _ hw ↦ taylor_coupledLiftStageSucc_X_eq e he hinv hhA hhB hU hV n (stage n) hw
  have hstabZ : ∀ n, ∀ w ∈ ReducedTensorWords.filtration R C n,
      reducedTransformationCochains.taylor (seqZ (n + 1)) w =
        reducedTransformationCochains.taylor (seqZ n) w :=
    fun n _ hw ↦ taylor_coupledLiftStageSucc_Z_eq e he hinv hhA hhB hU hV n (stage n) hw
  let X := reducedTransformationCochains.limit seqX hstabX
  let Z := reducedTransformationCochains.limit seqZ hstabZ
  refine ⟨X, Z, ?_, ?_⟩
  · apply Subtype.ext
    refine LinearMap.ext fun w ↦ ?_
    obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R C w
    have hbw := CC.barDifferential_mem_filtration hn
    have hXn :=
      reducedTransformationCochains.coe_limit_apply_of_mem_filtration (D := seqX) hstabX hn
    have hXnb :=
      reducedTransformationCochains.coe_limit_apply_of_mem_filtration (D := seqX) hstabX hbw
    have hzero := (stage n).hX w hn
    rw [reducedTransformationCochains.coe_sub, coe_reducedTransformationDifferential,
      LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.comp_apply] at hzero
    rw [coe_reducedTransformationDifferential, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, hXn, hXnb]
    exact (sub_eq_zero.1 hzero).symm
  · refine LinearMap.ext fun w ↦ ?_
    obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R C w
    have hbw := CC.barDifferential_mem_filtration hn
    have hXn :=
      reducedTransformationCochains.coe_limit_apply_of_mem_filtration (D := seqX) hstabX hn
    have hZn :=
      reducedTransformationCochains.coe_limit_apply_of_mem_filtration (D := seqZ) hstabZ hn
    have hZnb :=
      reducedTransformationCochains.coe_limit_apply_of_mem_filtration (D := seqZ) hstabZ hbw
    have hzero := (stage n).hZ w hn
    rw [reducedTransformationCochains.coe_sub, reducedTransformationCochains.coe_sub,
      reducedTransformationCochains.coe_compRight, coe_predDifferential,
      coe_reducedTransformationDifferential, LinearMap.sub_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.comp_apply] at hzero
    rw [reducedTransformationCochains.coe_compRight, coe_reducedTransformationDifferential,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, hXn, hZn, hZnb]
    exact (sub_eq_zero.1 hzero).symm

end LiftCompRight

end AInfinityHom

end TauCeti
