/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.Basic

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
degree-`p` map `Tᶜ(sA) ⟶ B` expands to a reduced transformation via
`AInfinityHom.reducedTransformationCochains.ofTaylor`.  The differential of a
reduced transformation is its graded commutator with the bar differentials,

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
transformations and commutes with the differential, inducing chain maps of complexes
`AInfinityHom.reducedTransformationComplexCompRight` and
`AInfinityHom.reducedTransformationComplexCompLeft`.

## Main definitions

* `TauCeti.AInfinityHom.reducedTransformationCochains`: the reduced transformations of degree `p`
  from `f` to `g`, the `(F, G)`-coderivations of degree `p` between reduced bar constructions.
* `TauCeti.AInfinityHom.reducedTransformationCochains.taylor` and
  `TauCeti.AInfinityHom.reducedTransformationCochains.ofTaylor`: the suspended Taylor components of
  a reduced transformation and its reconstruction from them.
* `TauCeti.AInfinityHom.reducedTransformationDifferential`: the graded commutator with the bar
  differentials.
* `TauCeti.AInfinityHom.reducedTransformationComplex`: the complex of reduced transformations from
  `f` to `g`.
* `TauCeti.AInfinityHom.reducedTransformationCochains.compRight`,
  `TauCeti.AInfinityHom.reducedTransformationCochains.compLeft`,
  `TauCeti.AInfinityHom.reducedTransformationComplexCompRight`, and
  `TauCeti.AInfinityHom.reducedTransformationComplexCompLeft`: composition of reduced
  transformations and their complexes with an `A∞` morphism after or before them.
* `TauCeti.AInfinityHom.Homotopy.equivCochains` and `TauCeti.AInfinityHom.Homotopy.ofTaylor`:
  homotopies from `f` to `g` as reduced transformations of degree `-1` bounding `F - G`, and
  construction of a homotopy from its suspended Taylor components.

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

/-- Reconstructs a reduced transformation of degree `p` from its suspended Taylor components: a
linear map `h : Tᶜ(sA) →ₗ[R] B` of suspended degree `p`. -/
noncomputable def ofTaylor (h : ReducedTensorWords R A →ₗ[R] B)
    (hh : LinearMap.IsHomogeneous h (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p) :
    reducedTransformationCochains f g p :=
  ⟨ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) p f.barMap g.barMap h,
    ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) p
      f.isCoalgHom_barMap g.isCoalgHom_barMap h,
    ReducedTensorWords.isHomogeneous_gradedCoderivAlong f.isHomogeneous_barMap
      g.isHomogeneous_barMap hh⟩

/-- The underlying map of bar constructions of `ofTaylor h hh` is `gradedCoderivAlong`. -/
@[simp]
theorem coe_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B)
    (hh : LinearMap.IsHomogeneous h (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p) :
    ((ofTaylor (f := f) (g := g) h hh : reducedTransformationCochains f g p) :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) =
      ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) p f.barMap g.barMap h :=
  (rfl)

/-- The Taylor components of `ofTaylor h hh` are `h`. -/
@[simp]
theorem taylor_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B)
    (hh : LinearMap.IsHomogeneous h (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece p) :
    taylor (ofTaylor (f := f) (g := g) h hh) = h :=
  ReducedTensorWords.letter_comp_gradedCoderivAlong (AA.grading.shift 1) p f.barMap g.barMap h

/-- Every reduced transformation is reconstructed from its own Taylor components. -/
@[simp]
theorem ofTaylor_taylor (D : reducedTransformationCochains f g p) :
    ofTaylor (taylor D) (isHomogeneous_taylor D) = D :=
  ext (taylor_ofTaylor _ _)

/-- Every reduced transformation preserves the conilpotence filtration. -/
theorem mem_filtration (D : reducedTransformationCochains f g p) {n : ℕ}
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.filtration R A n) :
    (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z ∈
      ReducedTensorWords.filtration R B n :=
  (isGradedCoderivationAlong D).mem_filtration f.isCoalgHom_barMap g.isCoalgHom_barMap hz

/-- Two reduced transformations whose Taylor components agree up to filtration level `n` agree on
the words of length at most `n`. -/
theorem apply_eq_of_mem_filtration {D D' : reducedTransformationCochains f g p} {n : ℕ}
    (hl : ∀ w ∈ ReducedTensorWords.filtration R A n, taylor D w = taylor D' w)
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.filtration R A n) :
    (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z =
      (D' : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z :=
  (isGradedCoderivationAlong D).apply_eq_of_mem_filtration (isGradedCoderivationAlong D') hl hz

/-- A reduced transformation whose Taylor components vanish up to filtration level `n` vanishes on
the words of length at most `n`. -/
theorem apply_eq_zero_of_mem_filtration {D : reducedTransformationCochains f g p} {n : ℕ}
    (hl : ∀ w ∈ ReducedTensorWords.filtration R A n, taylor D w = 0)
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.filtration R A n) :
    (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z = 0 :=
  (isGradedCoderivationAlong D).apply_eq_zero_of_mem_filtration hl hz

/-- A reduced transformation that vanishes up to filtration level `n` sends every word of length at
most `n + 1` to the single letter given by its Taylor component. -/
theorem apply_eq_ofLetter_of_mem_filtration_succ {D : reducedTransformationCochains f g p} {n : ℕ}
    (h₀ : ∀ u ∈ ReducedTensorWords.filtration R A n,
      (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) u = 0)
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.filtration R A (n + 1)) :
    (D : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) z =
      ReducedTensorWords.ofLetter R B (taylor D z) :=
  (isGradedCoderivationAlong D).apply_eq_ofLetter_of_mem_filtration_succ h₀ hz

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

/-- A degree-`p` cochain in `reducedTransformationComplex f g` is a cocycle if and only if its
`reducedTransformationDifferential` vanishes. -/
theorem mem_ker_reducedTransformationComplex_d_iff {f g : AInfinityHom AA BB} {p : ℤ}
    (D : (reducedTransformationComplex f g).X p) :
    D ∈ LinearMap.ker ((reducedTransformationComplex f g).d p (p + 1)).hom ↔
      reducedTransformationDifferential f g p D = 0 := by
  rw [LinearMap.mem_ker, reducedTransformationComplex_d]
  rfl

/-- Evaluating the differential of `reducedTransformationComplex f g` on `D` equals `E` if and
only if their underlying linear maps on `ReducedTensorWords` agree. -/
theorem reducedTransformationComplex_d_hom_eq_iff {f g : AInfinityHom AA BB} {p : ℤ}
    (D : (reducedTransformationComplex f g).X p)
    (E : (reducedTransformationComplex f g).X (p + 1)) :
    ((reducedTransformationComplex f g).d p (p + 1)).hom D = E ↔
      (reducedTransformationDifferential f g p D :
        ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = E.1 := by
  rw [reducedTransformationComplex_d]
  exact Subtype.ext_iff

/-- Subtraction in `(reducedTransformationComplex f g).X p` acts pointwise on the underlying
linear map. -/
@[simp]
theorem coe_reducedTransformationComplex_X_sub {f g : AInfinityHom AA BB} {p : ℤ}
    (D E : (reducedTransformationComplex f g).X p) :
    ((D - E : (reducedTransformationComplex f g).X p).1 :
      ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B) = D.1 - E.1 :=
  (rfl)

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

/-- Constructs a homotopy from `f` to `g` from its suspended Taylor components `h` of degree `-1`,
given the suspended component equation on single letters. -/
noncomputable def ofTaylor (h : ReducedTensorWords R A →ₗ[R] B)
    (hh : LinearMap.IsHomogeneous h (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    (e : f.taylor - g.taylor =
      BB.taylor ∘ₗ
        ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h +
        h ∘ₗ AA.barDifferential) :
    Homotopy f g :=
  ofCoderivation
    (ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h)
    (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong (AA.grading.shift 1) 1
      f.isCoalgHom_barMap g.isCoalgHom_barMap h)
    (ReducedTensorWords.isHomogeneous_gradedCoderivAlong f.isHomogeneous_barMap
      g.isHomogeneous_barMap hh)
    (by rwa [ReducedTensorWords.letter_comp_gradedCoderivAlong])

/-- The bar homotopy of `Homotopy.ofTaylor h hh e` is `gradedCoderivAlong` of `h`. -/
@[simp]
theorem barHomotopy_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh e) :
    (ofTaylor (f := f) (g := g) h hh e).barHomotopy =
      ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h := by
  rw [ofTaylor, barHomotopy_ofCoderivation]

/-- The Taylor components of `Homotopy.ofTaylor h hh e` are `h`. -/
@[simp]
theorem taylor_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh e) :
    (ofTaylor (f := f) (g := g) h hh e).taylor = h := by
  rw [ofTaylor, taylor_ofCoderivation, ReducedTensorWords.letter_comp_gradedCoderivAlong]

/-- Transports a homotopy along equalities of its source and target morphisms. -/
protected def cast {f' g' : AInfinityHom AA BB} (hf : f = f') (hg : g = g')
    (h : Homotopy f g) : Homotopy f' g' :=
  hf ▸ hg ▸ h

/-- Transporting a homotopy along morphism equalities preserves its bar homotopy. -/
@[simp]
theorem barHomotopy_cast {f' g' : AInfinityHom AA BB} (hf : f = f') (hg : g = g')
    (h : Homotopy f g) : (h.cast hf hg).barHomotopy = h.barHomotopy := by
  subst hf hg
  rfl

/-- Equal `A∞` morphisms are homotopic via the zero homotopy. -/
def ofEq (e : f = g) : Homotopy f g :=
  (refl f).cast rfl e

/-- The homotopy witnessing an equality of `A∞` morphisms has zero bar homotopy. -/
@[simp]
theorem barHomotopy_ofEq (e : f = g) : (ofEq e).barHomotopy = 0 := by
  subst e
  rw [ofEq, barHomotopy_cast, barHomotopy_refl]

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

section ComplexComp

universe u

variable {A' B' C' : Type u}
  [AddCommGroup A'] [Module R A']
  [AddCommGroup B'] [Module R B']
  [AddCommGroup C'] [Module R C']
  {AA' : AInfinityAlgebra R A'} {BB' : AInfinityAlgebra R B'} {CC' : AInfinityAlgebra R C'}

/-- Postcomposing reduced transformations with an `A∞` morphism `k` defines a chain map of
complexes of reduced transformations, when the carrier modules share a universe. -/
noncomputable def reducedTransformationComplexCompRight (f g : AInfinityHom AA' BB')
    (k : AInfinityHom BB' CC') :
    reducedTransformationComplex f g ⟶ reducedTransformationComplex (k.comp f) (k.comp g) where
  f p := ModuleCat.ofHom (reducedTransformationCochains.compRight k p)
  comm' := by
    rintro p _ (rfl : p + 1 = _)
    rw [reducedTransformationComplex_d, reducedTransformationComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun D ↦ reducedTransformationDifferential_compRight k D)

/-- In degree `p`, `reducedTransformationComplexCompRight f g k` is induced by
`reducedTransformationCochains.compRight k p`. -/
@[simp]
theorem reducedTransformationComplexCompRight_f (f g : AInfinityHom AA' BB')
    (k : AInfinityHom BB' CC') (p : ℤ) :
    (reducedTransformationComplexCompRight f g k).f p =
      (ModuleCat.ofHom (reducedTransformationCochains.compRight k p) :
        ModuleCat.of R _ ⟶ ModuleCat.of R _) :=
  (rfl)

/-- Evaluating `reducedTransformationComplexCompRight f g k` in degree `p` applies
`reducedTransformationCochains.compRight k p`. -/
theorem coe_reducedTransformationComplexCompRight_f_hom_apply (f g : AInfinityHom AA' BB')
    (k : AInfinityHom BB' CC') (p : ℤ) (D : (reducedTransformationComplex f g).X p) :
    (((reducedTransformationComplexCompRight f g k).f p).hom D).1 =
      (reducedTransformationCochains.compRight k p D :
        ReducedTensorWords R A' →ₗ[R] ReducedTensorWords R C') :=
  (rfl)

/-- Precomposing reduced transformations with an `A∞` morphism `k` defines a chain map of
complexes of reduced transformations, when the carrier modules share a universe. -/
noncomputable def reducedTransformationComplexCompLeft (f g : AInfinityHom AA' BB')
    (k : AInfinityHom CC' AA') :
    reducedTransformationComplex f g ⟶ reducedTransformationComplex (f.comp k) (g.comp k) where
  f p := ModuleCat.ofHom (reducedTransformationCochains.compLeft k p)
  comm' := by
    rintro p _ (rfl : p + 1 = _)
    rw [reducedTransformationComplex_d, reducedTransformationComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun D ↦ reducedTransformationDifferential_compLeft k D)

/-- In degree `p`, `reducedTransformationComplexCompLeft f g k` is induced by
`reducedTransformationCochains.compLeft k p`. -/
@[simp]
theorem reducedTransformationComplexCompLeft_f (f g : AInfinityHom AA' BB')
    (k : AInfinityHom CC' AA') (p : ℤ) :
    (reducedTransformationComplexCompLeft f g k).f p =
      (ModuleCat.ofHom (reducedTransformationCochains.compLeft k p) :
        ModuleCat.of R _ ⟶ ModuleCat.of R _) :=
  (rfl)

/-- Evaluating `reducedTransformationComplexCompLeft f g k` in degree `p` applies
`reducedTransformationCochains.compLeft k p`. -/
theorem coe_reducedTransformationComplexCompLeft_f_hom_apply (f g : AInfinityHom AA' BB')
    (k : AInfinityHom CC' AA') (p : ℤ) (D : (reducedTransformationComplex f g).X p) :
    (((reducedTransformationComplexCompLeft f g k).f p).hom D).1 =
      (reducedTransformationCochains.compLeft k p D :
        ReducedTensorWords R C' →ₗ[R] ReducedTensorWords R B') :=
  (rfl)

end ComplexComp

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

end AInfinityHom

end TauCeti
