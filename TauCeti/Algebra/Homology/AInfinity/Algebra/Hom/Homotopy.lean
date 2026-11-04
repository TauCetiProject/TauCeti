/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology
public import TauCeti.LinearAlgebra.TensorCoalgebra.Homotopy

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
`hₙ : A^{⊗ n} ⟶ B` of degree `-n` of the homotopy, and they determine it
(`TauCeti.AInfinityHom.Homotopy.ofTaylor`).  The homotopy equation is equivalent to its projection
onto single letters, the component equation `π ∘ (F - G) = π ∘ b_B ∘ H + π ∘ H ∘ b_A`: both sides
of the full equation are untwisted coderivations along `F` and `G`, and such a coderivation is
determined by its letter component
(`TauCeti.ReducedTensorWords.IsGradedCoderivationAlong.sub_eq_comp_add_comp_iff`).

In arity one the component equation says that `h₁` is a chain homotopy between the linear parts,
`f₁ - g₁ = m₁ h₁ + h₁ m₁`.  Consequently homotopic morphisms induce the same map on cohomology,
and one of them is a quasi-isomorphism exactly when the other is.  Homotopies can be composed with
morphisms on either side, composed vertically (`TauCeti.AInfinityHom.Homotopy.trans`), and reversed
(`TauCeti.AInfinityHom.Homotopy.symm`) by adding bar commutators with degree-`(-2)` biderivations
so as to restore the asymmetric Koszul-signed coderivation law.  Hence the homotopy relation
`TauCeti.AInfinityHom.Homotopic` is an equivalence relation compatible with composition.

## Main definitions

* `TauCeti.AInfinityHom.Homotopy`: a homotopy between two morphisms of `A∞` algebras.
* `TauCeti.AInfinityHom.Homotopy.taylor`: its suspended Taylor components.
* `TauCeti.AInfinityHom.Homotopy.linearHomotopy`: its arity-one component `h₁`.
* `TauCeti.AInfinityHom.Homotopy.ofCoderivation` and `TauCeti.AInfinityHom.Homotopy.ofTaylor`:
  the homotopy given by a coderivation or by suspended Taylor components of degree `-1` satisfying
  the component equation.
* `TauCeti.AInfinityHom.Homotopy.refl`, `TauCeti.AInfinityHom.Homotopy.symm`, and
  `TauCeti.AInfinityHom.Homotopy.trans`: reflexivity, symmetry, and transitivity of homotopies.
* `TauCeti.AInfinityHom.Homotopy.compRight`, `TauCeti.AInfinityHom.Homotopy.compLeft`, and
  `TauCeti.AInfinityHom.Homotopy.comp`: whiskering and horizontal composition of homotopies.
* `TauCeti.AInfinityHom.Homotopic` and `TauCeti.AInfinityHom.homotopicSetoid`: the equivalence
  relation of homotopy between `A∞` morphisms.

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
* `TauCeti.AInfinityHom.equivalence_homotopic`: homotopy of `A∞` morphisms is an equivalence
  relation.

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

theorem barHomotopy_eq_gradedCoderivAlong (h : Homotopy f g) :
    h.barHomotopy =
      ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h.taylor :=
  h.isGradedCoderivationAlong_barHomotopy.eq_gradedCoderivAlong f.isCoalgHom_barMap
    g.isCoalgHom_barMap

/-- Construct a homotopy from `f` to `g` from its suspended Taylor components `h` of degree `-1`. -/
noncomputable def ofTaylor (h : ReducedTensorWords R A →ₗ[R] B)
    (hh : LinearMap.IsHomogeneous h (ReducedTensorWords.gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece (-1))
    (e : f.taylor - g.taylor =
      BB.taylor ∘ₗ ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h
        + h ∘ₗ AA.barDifferential) : Homotopy f g :=
  ofCoderivation
    (ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h)
    (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong 1 f.isCoalgHom_barMap
      g.isCoalgHom_barMap h)
    (ReducedTensorWords.isHomogeneous_gradedCoderivAlong f.isHomogeneous_barMap
      g.isHomogeneous_barMap hh)
    (by rwa [ReducedTensorWords.letter_comp_gradedCoderivAlong])

@[simp] theorem barHomotopy_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh e) :
    (ofTaylor (f := f) (g := g) h hh e).barHomotopy =
      ReducedTensorWords.gradedCoderivAlong (AA.grading.shift 1) 1 f.barMap g.barMap h := (rfl)

@[simp] theorem taylor_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh e) :
    (ofTaylor (f := f) (g := g) h hh e).taylor = h := by
  rw [ofTaylor, taylor_ofCoderivation, ReducedTensorWords.letter_comp_gradedCoderivAlong]

/-! ### The arity-one component -/

/-- The arity-one component `h₁` of a homotopy: its Taylor component on single letters. -/
noncomputable def linearHomotopy (h : Homotopy f g) : A →ₗ[R] B :=
  h.taylor ∘ₗ ReducedTensorWords.ofLetter R A

@[simp]
theorem linearHomotopy_apply (h : Homotopy f g) (a : A) :
    h.linearHomotopy a = h.taylor (ReducedTensorWords.ofLetter R A a) := (rfl)

@[simp]
theorem linearHomotopy_ofTaylor (h : ReducedTensorWords R A →ₗ[R] B) (hh e) :
    (ofTaylor (f := f) (g := g) h hh e).linearHomotopy = h ∘ₗ ReducedTensorWords.ofLetter R A := by
  ext a
  rw [linearHomotopy_apply, taylor_ofTaylor, LinearMap.comp_apply]

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

/-! ### Identities, symmetry, and composition -/

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

@[simp] theorem linearHomotopy_refl (f : AInfinityHom AA BB) : (refl f).linearHomotopy = 0 := by
  simp only [linearHomotopy, taylor_refl, LinearMap.zero_comp]

/-- Reindex the source and target morphisms of a homotopy along propositional equalities. -/
def copy {f f' g g' : AInfinityHom AA BB} (h : Homotopy f g) (hf : f = f') (hg : g = g') :
    Homotopy f' g' where
  barHomotopy := h.barHomotopy
  isGradedCoderivationAlong_barHomotopy := by
    rw [← hf, ← hg]; exact h.isGradedCoderivationAlong_barHomotopy
  isHomogeneous_barHomotopy := h.isHomogeneous_barHomotopy
  barMap_sub_barMap := by rw [← hf, ← hg]; exact h.barMap_sub_barMap

@[simp] theorem barHomotopy_copy {f f' g g' : AInfinityHom AA BB} (h : Homotopy f g)
    (hf : f = f') (hg : g = g') : (h.copy hf hg).barHomotopy = h.barHomotopy := (rfl)
@[simp] theorem taylor_copy {f f' g g' : AInfinityHom AA BB} (h : Homotopy f g)
    (hf : f = f') (hg : g = g') : (h.copy hf hg).taylor = h.taylor := (rfl)
@[simp] theorem linearHomotopy_copy {f f' g g' : AInfinityHom AA BB} (h : Homotopy f g)
    (hf : f = f') (hg : g = g') : (h.copy hf hg).linearHomotopy = h.linearHomotopy := (rfl)

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

@[simp]
theorem linearHomotopy_compRight (h : Homotopy f g) (k : AInfinityHom BB CC) :
    (h.compRight k).linearHomotopy = k.linearPart ∘ₗ h.linearHomotopy := by
  ext a
  rw [linearHomotopy_apply, taylor_compRight, LinearMap.comp_apply, barHomotopy_ofLetter,
    ← k.linearPart_apply, LinearMap.comp_apply]

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

@[simp] theorem linearHomotopy_compLeft (h : Homotopy f g) (k : AInfinityHom CC AA) :
    (h.compLeft k).linearHomotopy = h.linearHomotopy ∘ₗ k.linearPart := by
  ext c; rw [linearHomotopy_apply, taylor_compLeft, LinearMap.comp_apply, k.barMap_ofLetter,
    ← h.linearHomotopy_apply, LinearMap.comp_apply]

/-- **Vertical composition of homotopies**, adding a biderivation commutator on bar maps. -/
noncomputable def trans {f g k : AInfinityHom AA BB} (h₁ : Homotopy f g) (h₂ : Homotopy g k) :
    Homotopy f k where
  barHomotopy := ReducedTensorWords.homotopyTrans (AA.grading.shift 1) f.barMap
    h₁.barHomotopy h₂.barHomotopy AA.barDifferential BB.barDifferential
  isGradedCoderivationAlong_barHomotopy :=
    ReducedTensorWords.isGradedCoderivationAlong_homotopyTrans
      f.isCoalgHom_barMap g.isCoalgHom_barMap f.isHomogeneous_barMap
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential
      BB.isGradedCoderivation_barDifferential
      f.barDifferential_comp_barMap k.barDifferential_comp_barMap
      h₁.isGradedCoderivationAlong_barHomotopy h₁.isHomogeneous_barHomotopy h₁.barMap_sub_barMap
      h₂.isGradedCoderivationAlong_barHomotopy h₂.isHomogeneous_barHomotopy h₂.barMap_sub_barMap
  isHomogeneous_barHomotopy := ReducedTensorWords.isHomogeneous_homotopyTrans f.isHomogeneous_barMap
    h₁.isHomogeneous_barHomotopy h₂.isHomogeneous_barHomotopy
    AA.isHomogeneous_barDifferential BB.isHomogeneous_barDifferential
  barMap_sub_barMap := ReducedTensorWords.homotopyTrans_eq AA.barDifferential_sq
    BB.barDifferential_sq h₁.barMap_sub_barMap h₂.barMap_sub_barMap

@[simp] theorem linearHomotopy_trans {f g k : AInfinityHom AA BB} (h₁ : Homotopy f g)
    (h₂ : Homotopy g k) :
    (h₁.trans h₂).linearHomotopy = h₁.linearHomotopy + h₂.linearHomotopy := by
  ext a; simp only [linearHomotopy_apply, LinearMap.add_apply, taylor_def, LinearMap.comp_apply,
    trans, ReducedTensorWords.homotopyTrans_ofLetter _ _ _ AA.isGradedCoderivation_barDifferential,
    map_add]

/-- **Symmetry of homotopies**, reversing the Koszul-signed coderivation law on bar maps. -/
noncomputable def symm {f g : AInfinityHom AA BB} (h : Homotopy f g) : Homotopy g f where
  barHomotopy := ReducedTensorWords.homotopySymm (AA.grading.shift 1) f.barMap h.barHomotopy
    AA.barDifferential BB.barDifferential
  isGradedCoderivationAlong_barHomotopy :=
    ReducedTensorWords.isGradedCoderivationAlong_homotopySymm
      f.isCoalgHom_barMap g.isCoalgHom_barMap f.isHomogeneous_barMap
      AA.isGradedCoderivation_barDifferential AA.isHomogeneous_barDifferential AA.barDifferential_sq
      BB.isGradedCoderivation_barDifferential BB.isHomogeneous_barDifferential BB.barDifferential_sq
      f.barDifferential_comp_barMap
      h.isGradedCoderivationAlong_barHomotopy h.isHomogeneous_barHomotopy h.barMap_sub_barMap
  isHomogeneous_barHomotopy := ReducedTensorWords.isHomogeneous_homotopySymm
    AA.isGradedCoderivation_barDifferential f.isHomogeneous_barMap h.isHomogeneous_barHomotopy
    AA.isHomogeneous_barDifferential BB.isHomogeneous_barDifferential
  barMap_sub_barMap := ReducedTensorWords.homotopySymm_eq AA.barDifferential_sq
    BB.barDifferential_sq h.barMap_sub_barMap

@[simp] theorem linearHomotopy_symm {f g : AInfinityHom AA BB} (h : Homotopy f g) :
    h.symm.linearHomotopy = -h.linearHomotopy := by
  ext a; simp only [linearHomotopy_apply, LinearMap.neg_apply, taylor_def, LinearMap.comp_apply,
    symm, ReducedTensorWords.homotopySymm_ofLetter _ _ AA.isGradedCoderivation_barDifferential,
    map_neg]

/-- Horizontal composition of homotopies: from `g₁ ∘ f₁` to `g₂ ∘ f₂`. -/
noncomputable def comp {g₁ g₂ : AInfinityHom BB CC} {f₁ f₂ : AInfinityHom AA BB}
    (hg : Homotopy g₁ g₂) (hf : Homotopy f₁ f₂) : Homotopy (g₁.comp f₁) (g₂.comp f₂) :=
  (hf.compRight g₁).trans (hg.compLeft f₂)

@[simp] theorem linearHomotopy_comp {g₁ g₂ : AInfinityHom BB CC} {f₁ f₂ : AInfinityHom AA BB}
    (hg : Homotopy g₁ g₂) (hf : Homotopy f₁ f₂) : (hg.comp hf).linearHomotopy =
      g₁.linearPart ∘ₗ hf.linearHomotopy + hg.linearHomotopy ∘ₗ f₂.linearPart := by
  rw [comp, linearHomotopy_trans, linearHomotopy_compRight, linearHomotopy_compLeft]

end Homotopy

/-! ### The homotopy relation -/

/-- Two `A∞` morphisms are **homotopic** when there exists a homotopy from the first to the
second. -/
def Homotopic (f g : AInfinityHom AA BB) : Prop := Nonempty (Homotopy f g)

/-- Two `A∞` morphisms are homotopic iff the type of homotopies between them is nonempty. -/
theorem homotopic_def (f g : AInfinityHom AA BB) : f.Homotopic g ↔ Nonempty (Homotopy f g) :=
  Iff.rfl

theorem Homotopy.homotopic {f g : AInfinityHom AA BB} (h : Homotopy f g) : f.Homotopic g := ⟨h⟩

namespace Homotopic

@[refl] theorem refl (f : AInfinityHom AA BB) : f.Homotopic f := ⟨Homotopy.refl f⟩
@[symm] theorem symm {f g : AInfinityHom AA BB} (h : f.Homotopic g) : g.Homotopic f :=
  let ⟨H⟩ := h; ⟨H.symm⟩
@[trans] theorem trans {f g k : AInfinityHom AA BB} (h₁ : f.Homotopic g) (h₂ : g.Homotopic k) :
    f.Homotopic k := let ⟨H₁⟩ := h₁; let ⟨H₂⟩ := h₂; ⟨H₁.trans H₂⟩

theorem compRight {f g : AInfinityHom AA BB} (h : f.Homotopic g) (k : AInfinityHom BB CC) :
    (k.comp f).Homotopic (k.comp g) := let ⟨H⟩ := h; ⟨H.compRight k⟩

theorem compLeft {f g : AInfinityHom AA BB} (h : f.Homotopic g) (k : AInfinityHom CC AA) :
    (f.comp k).Homotopic (g.comp k) := let ⟨H⟩ := h; ⟨H.compLeft k⟩

theorem comp {g₁ g₂ : AInfinityHom BB CC} {f₁ f₂ : AInfinityHom AA BB}
    (hg : g₁.Homotopic g₂) (hf : f₁.Homotopic f₂) : (g₁.comp f₁).Homotopic (g₂.comp f₂) :=
  let ⟨Hg⟩ := hg; let ⟨Hf⟩ := hf; ⟨Hg.comp Hf⟩

theorem cohomologyMap_eq {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.cohomologyMap = g.cohomologyMap := let ⟨H⟩ := h; H.cohomologyMap_eq

theorem isQuasiIso_iff {f g : AInfinityHom AA BB} (h : f.Homotopic g) :
    f.IsQuasiIso ↔ g.IsQuasiIso := let ⟨H⟩ := h; H.isQuasiIso_iff

end Homotopic

theorem equivalence_homotopic (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) :
    Equivalence (@Homotopic R A B _ _ _ _ _ AA BB) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

/-- The setoid of `A∞` morphisms modulo homotopy. -/
def homotopicSetoid (AA : AInfinityAlgebra R A) (BB : AInfinityAlgebra R B) :
    Setoid (AInfinityHom AA BB) := ⟨Homotopic, equivalence_homotopic AA BB⟩

end AInfinityHom

end TauCeti
