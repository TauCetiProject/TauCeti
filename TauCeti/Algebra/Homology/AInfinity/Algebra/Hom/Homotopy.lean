/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology

/-!
# Homotopies of morphisms of A-infinity algebras

Let `f g : A ⟶ B` be morphisms of `A∞` algebras, with bar maps `F` and `G` between the reduced
bar constructions `Tᶜ(sA)` and `Tᶜ(sB)`.  Following Keller, a *homotopy* from `f` to `g` is a
linear map `H : Tᶜ(sA) ⟶ Tᶜ(sB)` of degree `-1` which is a coderivation along `F` and `G`,

`Δ ∘ H = (H ⊗ G) ∘ Δ + (F ⊗ H) ∘ (τ ⊗ 1) ∘ Δ`,

with `τ` the letterwise Koszul twist of `Tᶜ(sA)`, and which satisfies the homotopy equation

`F - G = b_B ∘ H + H ∘ b_A`.

As for morphisms, the map on bar constructions is the stored datum.  Its suspended Taylor
components `π ∘ H`, for `π` the projection onto single letters, are the components
`hₙ : A^{⊗ n} ⟶ B` of degree `-n` of the homotopy, and they determine it.  The homotopy equation
is equivalent to its projection onto single letters, the component equation
`π ∘ (F - G) = π ∘ b_B ∘ H + π ∘ H ∘ b_A`: both sides of the full equation are untwisted
coderivations along `F` and `G`, and such a coderivation is determined by its letter component
(`TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_eq_comp_add_comp_iff`).

In arity one the component equation says that `h₁` is a chain homotopy between the linear parts,
`f₁ - g₁ = m₁ h₁ + h₁ m₁`.  Consequently homotopic morphisms induce the same map on cohomology,
and one of them is a quasi-isomorphism exactly when the other is.  Homotopies can be composed with
morphisms on either side.

## Main definitions

* `TauCeti.AInfinityHom.Homotopy`: a homotopy between two morphisms of `A∞` algebras.
* `TauCeti.AInfinityHom.Homotopy.taylor`: its suspended Taylor components.
* `TauCeti.AInfinityHom.Homotopy.linearHomotopy`: its arity-one component `h₁`.
* `TauCeti.AInfinityHom.Homotopy.ofCoderivation`: the homotopy given by a coderivation of degree
  `-1` along the bar maps which satisfies the component equation.
* `TauCeti.AInfinityHom.Homotopy.refl`: the zero homotopy from a morphism to itself.
* `TauCeti.AInfinityHom.Homotopy.compRight` and `TauCeti.AInfinityHom.Homotopy.compLeft`:
  composition of a homotopy with a morphism after it or before it.

## Main results

* `TauCeti.AInfinityHom.barMap_sub_barMap_iff`: the homotopy equation holds exactly when its
  letter component does.
* `TauCeti.AInfinityHom.Homotopy.ext`: a homotopy is determined by its Taylor components.
* `TauCeti.AInfinityHom.Homotopy.taylor_sub_taylor`: the component equation.
* `TauCeti.AInfinityHom.Homotopy.linearPart_sub_linearPart`: the arity-one component is a chain
  homotopy between the linear parts.
* `TauCeti.AInfinityHom.Homotopy.cohomologyMap_eq`: homotopic morphisms induce the same map on
  cohomology.
* `TauCeti.AInfinityHom.Homotopy.isQuasiIso_iff`: homotopic morphisms are quasi-isomorphisms
  together.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1.
-/

public section

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- A homotopy from the `A∞` morphism `f` to the `A∞` morphism `g`, stored as a map of reduced bar
constructions: a coderivation along the bar maps of `f` and `g`, of degree `-1` for the suspended
gradings, whose bar commutator is the difference of the bar maps.  Its suspended Taylor components
are `AInfinityHom.Homotopy.taylor`. -/
structure Homotopy (f g : AInfinityHom AA BB) where
  /-- The homotopy on reduced bar constructions. -/
  barHomotopy : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B
  /-- The homotopy is an odd coderivation along the bar maps of `f` and `g`. -/
  isGradedCoderivationAlong_barHomotopy :
    ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) 1 f.barMap g.barMap
      barHomotopy
  /-- The homotopy has degree `-1` for the suspended gradings. -/
  isHomogeneous_barHomotopy : LinearMap.IsHomogeneous barHomotopy
    (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
    (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (-1)
  /-- The homotopy equation `F - G = b_B ∘ H + H ∘ b_A`. -/
  barMap_sub_barMap :
    f.barMap - g.barMap = BB.barDifferential ∘ₗ barHomotopy + barHomotopy ∘ₗ AA.barDifferential

/-! ### The component equation -/

/-- **The homotopy equation is equivalent to its projection onto single letters.**  For a
coderivation `H` of degree `-1` along the bar maps of `f` and `g`, the equation
`F - G = b_B ∘ H + H ∘ b_A` holds exactly when its letter component, the suspended component
equation, holds. -/
theorem barMap_sub_barMap_iff {f g : AInfinityHom AA BB}
    {H : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B}
    (hH : ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) 1 f.barMap g.barMap H)
    (hH₁ : LinearMap.IsHomogeneous H (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (-1)) :
    f.barMap - g.barMap = BB.barDifferential ∘ₗ H + H ∘ₗ AA.barDifferential ↔
      f.taylor - g.taylor = BB.taylor ∘ₗ H +
        (ReducedTensorWords.letter R B ∘ₗ H) ∘ₗ AA.barDifferential := by
  simpa only [LinearMap.comp_sub, LinearMap.comp_add, ← LinearMap.comp_assoc,
    BB.letter_comp_barDifferential, AInfinityHom.taylor_def] using
    hH.sub_eq_comp_add_comp_iff hH₁ (by decide) AA.isGradedCoderivation_barDifferential
    AA.isHomogeneous_barDifferential (by decide) BB.isGradedCoderivation_barDifferential
    f.isCoalgHom_barMap g.isCoalgHom_barMap f.isHomogeneous_barMap
    f.barDifferential_comp_barMap g.barDifferential_comp_barMap

namespace Homotopy

variable {f g : AInfinityHom AA BB}

/-- The homotopy equation, applied to an element. -/
theorem barMap_sub_barMap_apply (h : Homotopy f g) (z : ReducedTensorWords R A) :
    f.barMap z - g.barMap z =
      BB.barDifferential (h.barHomotopy z) + h.barHomotopy (AA.barDifferential z) :=
  LinearMap.congr_fun h.barMap_sub_barMap z

/-- Homotopies are determined by their maps of bar constructions. -/
theorem barHomotopy_injective :
    Function.Injective (barHomotopy : Homotopy f g → _) := by
  rintro ⟨H, _, _, _⟩ ⟨H', _, _, _⟩ e
  cases e
  rfl

/-! ### Taylor components -/

/-- The suspended Taylor components of a homotopy: its map of bar constructions followed by the
projection onto single letters.  On words of length `n` this is the suspension of the component
`hₙ`. -/
noncomputable def taylor (h : Homotopy f g) : ReducedTensorWords R A →ₗ[R] B :=
  ReducedTensorWords.letter R B ∘ₗ h.barHomotopy

theorem taylor_def (h : Homotopy f g) :
    h.taylor = ReducedTensorWords.letter R B ∘ₗ h.barHomotopy := (rfl)

/-- The Taylor components of a homotopy have degree `-1` for the suspended gradings. -/
theorem isHomogeneous_taylor (h : Homotopy f g) :
    LinearMap.IsHomogeneous h.taylor (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1) := by
  rw [taylor_def]
  simpa only [add_zero] using
    (ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1)).comp h.isHomogeneous_barHomotopy

/-- Homotopies between the same morphisms are determined by their Taylor components. -/
theorem taylor_injective : Function.Injective (taylor : Homotopy f g → _) := fun h h' e ↦
  barHomotopy_injective <| h.isGradedCoderivationAlong_barHomotopy.eq_of_letter_comp_eq
    h'.isGradedCoderivationAlong_barHomotopy e

/-- Two homotopies between the same morphisms with the same Taylor components are equal. -/
@[ext]
theorem ext {h h' : Homotopy f g} (e : h.taylor = h'.taylor) : h = h' :=
  taylor_injective e

/-! ### Component equations -/

/-- The suspended component equation of a homotopy: the difference of the Taylor components of
`f` and `g` is the Taylor map of the target after the homotopy plus the Taylor components of the
homotopy after the bar differential of the source.  On words of length `n` this is the arity-`n`
relation between the components `fᵢ`, `gᵢ`, `hᵢ` and the operations `mⱼ`. -/
theorem taylor_sub_taylor (h : Homotopy f g) :
    f.taylor - g.taylor = BB.taylor ∘ₗ h.barHomotopy + h.taylor ∘ₗ AA.barDifferential :=
  (barMap_sub_barMap_iff h.isGradedCoderivationAlong_barHomotopy
    h.isHomogeneous_barHomotopy).1 h.barMap_sub_barMap

/-- The homotopy from `f` to `g` given by a coderivation `H` of degree `-1` along their bar maps
whose letter component satisfies the suspended component equation.  The full homotopy equation
follows, since a coderivation along the bar maps is determined by its letter component. -/
noncomputable def ofCoderivation (H : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)
    (hH : ReducedTensorWords.IsGradedCoderivationAlong (AA.grading.shift 1) 1 f.barMap g.barMap H)
    (hH₁ : LinearMap.IsHomogeneous H (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (-1))
    (e : f.taylor - g.taylor = BB.taylor ∘ₗ H +
      (ReducedTensorWords.letter R B ∘ₗ H) ∘ₗ AA.barDifferential) :
    Homotopy f g where
  barHomotopy := H
  isGradedCoderivationAlong_barHomotopy := hH
  isHomogeneous_barHomotopy := hH₁
  barMap_sub_barMap := (barMap_sub_barMap_iff hH hH₁).2 e

@[simp]
theorem barHomotopy_ofCoderivation (H : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)
    (hH hH₁ e) : (ofCoderivation (f := f) (g := g) H hH hH₁ e).barHomotopy = H := (rfl)

/-- The Taylor components of a homotopy constructed from a coderivation are its letter component. -/
@[simp]
theorem taylor_ofCoderivation (H : ReducedTensorWords R A →ₗ[R] ReducedTensorWords R B)
    (hH hH₁ e) : (ofCoderivation (f := f) (g := g) H hH hH₁ e).taylor =
      ReducedTensorWords.letter R B ∘ₗ H := (rfl)

/-! ### The arity-one component -/

/-- The arity-one component `h₁` of a homotopy: its Taylor component on single letters. -/
noncomputable def linearHomotopy (h : Homotopy f g) : A →ₗ[R] B :=
  h.taylor ∘ₗ ReducedTensorWords.ofLetter R A

@[simp]
theorem linearHomotopy_apply (h : Homotopy f g) (a : A) :
    h.linearHomotopy a = h.taylor (ReducedTensorWords.ofLetter R A a) := (rfl)

/-- A homotopy sends a single letter to the single letter given by its arity-one component: a
coderivation along coalgebra maps sends primitives to primitives. -/
@[simp]
theorem barHomotopy_ofLetter (h : Homotopy f g) (a : A) :
    h.barHomotopy (ReducedTensorWords.ofLetter R A a) =
      ReducedTensorWords.ofLetter R B (h.linearHomotopy a) := by
  have hd : ReducedTensorWords.deconcatenation R B
      (h.barHomotopy (ReducedTensorWords.ofLetter R A a)) = 0 := by
    rw [h.isGradedCoderivationAlong_barHomotopy.deconcatenation_apply,
      ReducedTensorWords.deconcatenation_ofLetter, map_zero, map_zero, map_zero, add_zero]
  obtain ⟨y, hy⟩ := (ReducedTensorWords.deconcatenation_eq_zero_iff R B).1 hd
  rw [linearHomotopy_apply, taylor_def, LinearMap.comp_apply, ← hy,
    ReducedTensorWords.letter_ofLetter]

/-- The arity-one component of a homotopy lowers the internal degree by one. -/
theorem linearHomotopy_mem (h : Homotopy f g) {p : ℤ} {a : A}
    (ha : a ∈ AA.grading.piece p) : h.linearHomotopy a ∈ BB.grading.piece (p - 1) := by
  have ha' : a ∈ (AA.grading.shift 1).piece (p - 1) := by
    rwa [InternalGrading.shift_piece, sub_add_cancel]
  have hh := h.isHomogeneous_taylor.map_mem
    (ReducedTensorWords.ofLetter_mem_gradedPiece (AA.grading.shift 1) ha')
  -- Homogeneity gives suspended degree `(p - 1) + -1`; `shift_piece` adds 1 back.
  -- This index is not definitionally equal to `p - 1`, so normalize it explicitly with `ring`.
  rwa [InternalGrading.shift_piece, show p - 1 + -1 + 1 = p - 1 by ring] at hh

/-- **The arity-one component is a chain homotopy between the linear parts**:
`f₁ - g₁ = m₁ h₁ + h₁ m₁`.  This is the arity-one component of the homotopy equation. -/
theorem linearPart_sub_linearPart (h : Homotopy f g) (a : A) :
    f.linearPart a - g.linearPart a =
      BB.m 1 ![h.linearHomotopy a] + h.linearHomotopy (AA.m 1 ![a]) := by
  have e := congrArg (ReducedTensorWords.letter R B)
    (h.barMap_sub_barMap_apply (ReducedTensorWords.ofLetter R A a))
  simpa only [map_sub, map_add, barMap_ofLetter, barHomotopy_ofLetter,
    AInfinityAlgebra.barDifferential_ofLetter, ReducedTensorWords.letter_ofLetter] using e

/-! ### Cohomology -/

/-- **Homotopic `A∞` morphisms induce the same map on cohomology.** -/
theorem cohomologyMap_eq (h : Homotopy f g) : f.cohomologyMap = g.cohomologyMap := by
  ext x
  obtain ⟨u, hu, rfl⟩ := AA.exists_cohomologyClass_eq x
  rw [cohomologyMap_cohomologyClass, cohomologyMap_cohomologyClass, BB.cohomologyClass_eq_iff,
    h.linearPart_sub_linearPart, AA.mem_cycles.1 hu, map_zero, add_zero]
  exact BB.mem_boundaries.2 ⟨_, rfl⟩

/-- Homotopic `A∞` morphisms are quasi-isomorphisms together. -/
theorem isQuasiIso_iff (h : Homotopy f g) : f.IsQuasiIso ↔ g.IsQuasiIso := by
  rw [isQuasiIso_def, isQuasiIso_def, h.cohomologyMap_eq]

/-! ### Identities and composition -/

/-- The zero homotopy from an `A∞` morphism to itself. -/
def refl (f : AInfinityHom AA BB) : Homotopy f f where
  barHomotopy := 0
  isGradedCoderivationAlong_barHomotopy :=
    ReducedTensorWords.isGradedCoderivationAlong_zero _ _ _ _
  isHomogeneous_barHomotopy := LinearMap.isHomogeneous_zero _ _ _
  barMap_sub_barMap := by
    rw [LinearMap.comp_zero, LinearMap.zero_comp, add_zero]
    exact sub_self f.barMap

@[simp]
theorem barHomotopy_refl (f : AInfinityHom AA BB) : (refl f).barHomotopy = 0 := (rfl)

/-- The zero homotopy has zero Taylor components. -/
@[simp]
theorem taylor_refl (f : AInfinityHom AA BB) : (refl f).taylor = 0 := by
  simp only [taylor_def, barHomotopy_refl, LinearMap.comp_zero]

/-- A homotopy from `f` to `g` followed by an `A∞` morphism `k`: a homotopy from `k ∘ f` to
`k ∘ g`. -/
def compRight (h : Homotopy f g) (k : AInfinityHom BB CC) : Homotopy (k.comp f) (k.comp g) where
  barHomotopy := k.barMap ∘ₗ h.barHomotopy
  isGradedCoderivationAlong_barHomotopy := by
    simpa only [barMap_comp] using
      k.isCoalgHom_barMap.comp_isGradedCoderivationAlong h.isGradedCoderivationAlong_barHomotopy
  isHomogeneous_barHomotopy := by
    simpa only [add_zero] using k.isHomogeneous_barMap.comp h.isHomogeneous_barHomotopy
  barMap_sub_barMap := by
    rw [barMap_comp, barMap_comp, ← LinearMap.comp_sub, h.barMap_sub_barMap]
    simp only [LinearMap.comp_add, ← LinearMap.comp_assoc, ← k.barDifferential_comp_barMap]

@[simp]
theorem barHomotopy_compRight (h : Homotopy f g) (k : AInfinityHom BB CC) :
    (h.compRight k).barHomotopy = k.barMap ∘ₗ h.barHomotopy := (rfl)

/-- Postcomposition computes the Taylor components using the Taylor map of the morphism. -/
theorem taylor_compRight (h : Homotopy f g) (k : AInfinityHom BB CC) :
    (h.compRight k).taylor = k.taylor ∘ₗ h.barHomotopy := by
  simp only [taylor_def, barHomotopy_compRight, AInfinityHom.taylor_def, LinearMap.comp_assoc]

/-- An `A∞` morphism `k` followed by a homotopy from `f` to `g`: a homotopy from `f ∘ k` to
`g ∘ k`. -/
def compLeft (h : Homotopy f g) (k : AInfinityHom CC AA) : Homotopy (f.comp k) (g.comp k) where
  barHomotopy := h.barHomotopy ∘ₗ k.barMap
  isGradedCoderivationAlong_barHomotopy := by
    simpa only [barMap_comp] using
      h.isGradedCoderivationAlong_barHomotopy.comp_isCoalgHom k.isCoalgHom_barMap
        k.isHomogeneous_barMap
  isHomogeneous_barHomotopy := by
    simpa only [zero_add] using h.isHomogeneous_barHomotopy.comp k.isHomogeneous_barMap
  barMap_sub_barMap := by
    rw [barMap_comp, barMap_comp, ← LinearMap.sub_comp, h.barMap_sub_barMap]
    simp only [LinearMap.add_comp, LinearMap.comp_assoc, k.barDifferential_comp_barMap]

@[simp]
theorem barHomotopy_compLeft (h : Homotopy f g) (k : AInfinityHom CC AA) :
    (h.compLeft k).barHomotopy = h.barHomotopy ∘ₗ k.barMap := (rfl)

/-- Precomposition computes the Taylor components using the bar map of the morphism. -/
theorem taylor_compLeft (h : Homotopy f g) (k : AInfinityHom CC AA) :
    (h.compLeft k).taylor = h.taylor ∘ₗ k.barMap := (rfl)

end Homotopy

end AInfinityHom

end TauCeti
