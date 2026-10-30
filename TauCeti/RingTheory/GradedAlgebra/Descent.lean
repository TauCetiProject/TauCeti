/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import TauCeti.RingTheory.Flat.EffectiveDescent
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Maps
public import TauCeti.RingTheory.GradedAlgebra.Subalgebra

/-!
# Effective descent for graded algebras

Let `S` be an `R`-algebra and let `D` be a descent datum, in the sense of
`TauCeti.Algebra.DescentDatum R S B`, on an `S`-algebra `B` graded by `ℬ : ι → Submodule S B`.
The datum is *graded* (`TauCeti.Algebra.DescentDatum.IsGraded`) when its coaction
`θ : B → S ⊗[R] B` maps each piece `ℬ i` into `S ⊗[R] ℬ i`; in terms of the gluing isomorphism
`B ⊗[R] S ≅ S ⊗[R] B`, the isomorphism preserves degrees.

For a graded datum the homogeneous components of an invariant element are invariant, so the
descended `R`-algebra `D.descended = {b | θ b = 1 ⊗ b}` is graded by its intersections with the
pieces of `ℬ`. When `S` is flat over `R`, the effectivity isomorphism
`D.baseChangeEquiv : S ⊗[R] D.descended ≃ₐ[S] B` is then an isomorphism of graded algebras: it
identifies `S ⊗[R] (D.descended ∩ ℬ i)` with `ℬ i` for every `i`. Thus graded descent data are
effective in the category of graded algebras.

Graded descent data arise on homogeneous coordinate rings: over an affine base, a descent datum
on a projective scheme `X` together with a compatible descent datum on a relatively ample line
bundle `L` induces a graded descent datum on the section ring `⨁ₙ Γ(X, Lⁿ)`. The projective
spectrum of `B` is then the base change of the projective spectrum of the descended graded
algebra (`TauCeti.AlgebraicGeometry.Descent.Proj`).

## Main definitions

* `TauCeti.Algebra.DescentDatum.IsGraded D ℬ`: the coaction of `D` preserves the grading `ℬ`.
* `TauCeti.Algebra.DescentDatum.gradedCoaction D ℬ`: the coaction as a homomorphism of graded
  algebras `B → S ⊗[R] B`.
* `TauCeti.Algebra.DescentDatum.descendedGrading D ℬ`: the grading of the descended algebra, a
  graded algebra when `D` is graded.

## Main results

* `TauCeti.Algebra.DescentDatum.isHomogeneous_descended`: the descended algebra of a graded
  descent datum is a homogeneous subalgebra.
* `TauCeti.Algebra.DescentDatum.baseChangeEquiv_mem_iff`: **effectivity of graded descent.** If
  `S` is flat over `R`, the effectivity isomorphism `S ⊗[R] D.descended ≃ B` carries the degree-`i`
  piece `S ⊗[R] (D.descended ∩ ℬ i)` exactly onto `ℬ i`.
* `TauCeti.Algebra.DescentDatum.isGraded_baseChange`: the canonical descent datum on the base
  change `S ⊗[R] A` of a graded `R`-algebra is graded.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII, §7
  (effectivity of descent data in the presence of an ample invertible sheaf).
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open TensorProduct DirectSum

namespace TauCeti

namespace Algebra

namespace DescentDatum

section Semiring

variable {ι R S B : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [CommSemiring S]
  [Algebra R S] [Semiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- A descent datum on a graded algebra `B` is *graded* when its coaction `B → S ⊗[R] B` maps
each homogeneous piece `ℬ i` into `S ⊗[R] ℬ i`. -/
class IsGraded (D : DescentDatum R S B) (ℬ : ι → Submodule S B) : Prop where
  /-- The coaction maps the degree-`i` piece into its base change. -/
  coaction_mem {i : ι} {b : B} : b ∈ ℬ i → D.coaction b ∈ ((ℬ i).restrictScalars R).baseChange S

variable (D : DescentDatum R S B) (ℬ : ι → Submodule S B)

/-- The grading of the descended algebra: its degree-`i` piece consists of the invariant
elements which lie in `ℬ i`. -/
abbrev descendedGrading (i : ι) : Submodule R D.descended :=
  D.descended.grading (ℬ · |>.restrictScalars R) i

omit [DecidableEq ι] [AddMonoid ι] in
theorem mem_descendedGrading_iff {i : ι} {a : D.descended} :
    a ∈ D.descendedGrading ℬ i ↔ (a : B) ∈ ℬ i :=
  Subalgebra.mem_grading_iff _ _

/-- The inclusion of the descended algebra into `B`, as a homomorphism of graded rings. -/
def descendedGradedVal : D.descendedGrading ℬ →+*ᵍ ℬ where
  __ := (D.descended.val : D.descended →+* B)
  map_mem := D.mem_descendedGrading_iff ℬ |>.mp

omit [DecidableEq ι] [AddMonoid ι] in
@[simp]
theorem coe_descendedGradedVal : ⇑(D.descendedGradedVal ℬ) = Subtype.val :=
  (rfl)

omit [DecidableEq ι] [AddMonoid ι] in
/-- The inclusion of the descended graded algebra commutes with the structure maps from `R`. -/
theorem descendedGradedVal_algebraMap (r : R) :
    D.descendedGradedVal ℬ (algebraMap R D.descended r) = algebraMap R B r :=
  D.descended.val.commutes r

variable [GradedAlgebra ℬ] [D.IsGraded ℬ]

/-- The coaction of a graded descent datum, as a homomorphism of graded `S`-algebras from `B` to
`S ⊗[R] B` with the base-changed grading. -/
def gradedCoaction : ℬ →ₐᵍ[S] fun i ↦ ((ℬ i).restrictScalars R).baseChange S where
  __ := D.coaction
  map_mem := IsGraded.coaction_mem

@[simp]
theorem coe_gradedCoaction : ⇑(D.gradedCoaction ℬ) = D.coaction :=
  (rfl)

/-- The coaction of a graded descent datum commutes with taking homogeneous components. -/
theorem coaction_decompose (b : B) (i : ι) :
    D.coaction (decompose ℬ b i) =
      decompose (fun i ↦ ((ℬ i).restrictScalars R).baseChange S) (D.coaction b) i :=
  (D.gradedCoaction ℬ).map_directSumDecompose

/-- The descended algebra of a graded descent datum is homogeneous: every homogeneous component
of an invariant element is invariant. -/
theorem isHomogeneous_descended :
    SetLike.IsHomogeneous (ℬ · |>.restrictScalars R) D.descended := by
  intro i b hb
  rw [mem_descended_iff] at hb ⊢
  -- The right tensor inclusion is graded, so it also commutes with homogeneous components.
  have h1 : (1 : S) ⊗ₜ[R] (decompose ℬ b i : B) =
      decompose (fun i ↦ ((ℬ i).restrictScalars R).baseChange S) ((1 : S) ⊗ₜ[R] b) i :=
    (GradedAlgHom.includeRight S (ℬ · |>.restrictScalars R)).map_directSumDecompose
  exact (D.coaction_decompose ℬ b i).trans (hb ▸ h1.symm)

/-- The descended algebra of a graded descent datum is graded by its intersections with the
pieces of `ℬ`. -/
noncomputable instance instGradedAlgebraDescendedGrading : GradedAlgebra (D.descendedGrading ℬ) :=
  Subalgebra.gradedAlgebra (D.isHomogeneous_descended ℬ)

omit [DecidableEq ι] [AddMonoid ι] in
/-- The canonical descent datum `s ⊗ a ↦ s ⊗ (1 ⊗ a)` on the base change `S ⊗[R] A` of an
`R`-algebra graded by `𝒜` is graded for the base-changed grading `S ⊗[R] 𝒜 i`. -/
instance isGraded_baseChange {A : Type*} [Semiring A] [Algebra R A] (𝒜 : ι → Submodule R A) :
    (baseChange R S A).IsGraded fun i ↦ (𝒜 i).baseChange S where
  coaction_mem {i x} hx := by
    obtain ⟨x, rfl⟩ := Submodule.toBaseChange_surjective' _ _ hx
    clear hx
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      simpa using Submodule.tmul_mem_baseChange_of_mem (R := R)
        (p := ((𝒜 i).baseChange S).restrictScalars R) s
        (Submodule.tmul_mem_baseChange_of_mem (R := R) (1 : S) a.2)
    | add x y hx hy => simpa using add_mem hx hy

end Semiring

section Ring

variable {ι R S B : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing R] [CommRing S]
  [Algebra R S] [Ring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  (D : DescentDatum R S B) (ℬ : ι → Submodule S B) [GradedAlgebra ℬ] [D.IsGraded ℬ]

/-- The comparison `s ⊗ a ↦ s • a` from the base change of the descended graded algebra, as a
homomorphism of graded `S`-algebras. -/
private noncomputable def gradedBaseChangeHom :
    (fun i ↦ (D.descendedGrading ℬ i).baseChange S) →ₐᵍ[S] ℬ :=
  GradedAlgHom.liftEquiv _ _ (Subalgebra.gradedVal D.descended (ℬ · |>.restrictScalars R))

private theorem coe_gradedBaseChangeHom [Module.Flat R S] :
    ⇑(D.gradedBaseChangeHom ℬ) = D.baseChangeEquiv := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp [gradedBaseChangeHom]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **Effectivity of graded descent.** If `S` is flat over `R`, the effectivity isomorphism
`S ⊗[R] D.descended ≃ₐ[S] B` of a graded descent datum is an isomorphism of graded algebras: it
carries `S ⊗[R] (D.descended ∩ ℬ i)` exactly onto `ℬ i`. -/
@[simp]
theorem baseChangeEquiv_mem_iff [Module.Flat R S] {x : S ⊗[R] D.descended} {i : ι} :
    D.baseChangeEquiv x ∈ ℬ i ↔ x ∈ (D.descendedGrading ℬ i).baseChange S := by
  rw [← D.coe_gradedBaseChangeHom ℬ]
  exact Graded.map_mem_iff_of_injective _
    (D.coe_gradedBaseChangeHom ℬ ▸ D.baseChangeEquiv.injective)

end Ring

end DescentDatum

end Algebra

end TauCeti
