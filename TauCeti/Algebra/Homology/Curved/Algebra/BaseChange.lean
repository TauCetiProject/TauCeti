/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.BaseChange

/-!
# Base change of curved differential graded algebras

Let `(A, d, w)` be a curved differential graded algebra over a commutative ring `R`, and let `S`
be a commutative `R`-algebra. The base change `S ⊗[R] A`, graded by the base changes
`S ⊗[R] Aᵖ` of the homogeneous pieces (Mathlib's `GradedAlgebra.baseChange`), with differential
`1 ⊗ d` and curvature `1 ⊗ w`, is a curved differential graded algebra over `S`. No flatness of
`S` is needed: every axiom is an identity between `R`-multilinear expressions in homogeneous
elements, and these are preserved by `S ⊗[R] -`. The degree law and the graded Leibniz rule are
transported by the lemmas shared with the base change of ordinary differential graded algebras in
`TauCeti.Algebra.Homology.DG.Algebra.BaseChange`.

Conversely, a curved differential graded `S`-algebra restricts to one over `R` with the same
differential and curvature. Base change is left adjoint to this restriction on strict curved
morphisms: strict curved `R`-morphisms `A → B` correspond to strict curved `S`-morphisms
`S ⊗[R] A → B`, extending the graded adjunction `GradedAlgHom.liftEquiv` of Mathlib. The unit of
the adjunction is the inclusion `a ↦ 1 ⊗ a`. In particular base change acts on strict curved
morphisms, functorially.

## Main definitions

* `TauCeti.CurvedDGAlgHom.includeRight`: the strict curved morphism `a ↦ 1 ⊗ a` from `A` to its
  base change, regarded over `R`.
* `TauCeti.CurvedDGAlgHom.liftEquiv`: the base change–restriction adjunction on strict curved
  morphisms.
* `TauCeti.CurvedDGAlgHom.baseChange`: the base change `s ⊗ a ↦ s ⊗ f a` of a strict curved
  morphism.

## Main results

* `TauCeti.IsCurvedDGAlgebra.baseChange`: the base change of a curved differential graded
  algebra, with differential `1 ⊗ d` and curvature `1 ⊗ w`.
* `TauCeti.IsCurvedDGAlgebra.restrictScalars`: restriction of scalars of a curved differential
  graded algebra.
* `TauCeti.CurvedDGAlgHom.baseChange_ext`: strict curved morphisms out of a base change are
  determined on the elements `1 ⊗ a`.
* `TauCeti.CurvedDGAlgHom.baseChange_id` and `TauCeti.CurvedDGAlgHom.baseChange_comp`:
  functoriality of base change.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2, for
  curved DG algebras. The curvature here is the negative of his, as in `IsCurvedDGAlgebra`.
-/

public section

open TensorProduct

namespace TauCeti

section BaseChange

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Type*) [CommRing S] [Algebra R S]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- **Base change.** For a commutative `R`-algebra `S`, the base change `S ⊗[R] A` of a curved
differential graded `R`-algebra, graded by the base changes of the homogeneous pieces, is a curved
differential graded `S`-algebra with differential `1 ⊗ d` and curvature `1 ⊗ w`. -/
theorem IsCurvedDGAlgebra.baseChange (h : IsCurvedDGAlgebra 𝒜 d w) :
    IsCurvedDGAlgebra (fun p ↦ (𝒜 p).baseChange S) (d.baseChange S) (1 ⊗ₜ[R] w) where
  map_mem := map_mem_baseChange_of_map_mem S h.map_mem
  leibniz := leibniz_baseChange_of_leibniz S h.leibniz
  curvature_mem := Submodule.tmul_mem_baseChange_of_mem 1 h.curvature_mem
  sq_eq x := by
    induction x with
    | add x y hx hy => simp only [map_add, hx, hy, add_mul, mul_add]; abel
    | tmul s a => simp [h.sq_eq a, tmul_sub]
  map_curvature := by simp [h.map_curvature]

end BaseChange

section RestrictScalars

variable (R : Type*) {S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [Ring B] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] {ℬ : ℤ → Submodule S B} [GradedAlgebra ℬ]
  {d : B →ₗ[S] B} {w : B}

/-- **Restriction of scalars.** A curved differential graded `S`-algebra is a curved
differential graded `R`-algebra, with the same pieces, differential and curvature. -/
theorem IsCurvedDGAlgebra.restrictScalars (h : IsCurvedDGAlgebra ℬ d w) :
    IsCurvedDGAlgebra (ℬ · |>.restrictScalars R) (d.restrictScalars R) w where
  map_mem := h.map_mem
  leibniz := h.leibniz
  curvature_mem := h.curvature_mem
  sq_eq := h.sq_eq
  map_curvature := h.map_curvature

end RestrictScalars

namespace CurvedDGAlgHom

variable {R A B : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Ring A] [Algebra R A] {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A} {wA : A}

/-- The inclusion `a ↦ 1 ⊗ a` of a curved differential graded `R`-algebra into its base change to
`S`, regarded over `R`, is a strict curved morphism. It is the unit of the adjunction
`CurvedDGAlgHom.liftEquiv`. -/
def includeRight (hA : IsCurvedDGAlgebra 𝒜 dA wA) :
    CurvedDGAlgHom hA ((hA.baseChange S).restrictScalars R) where
  toGradedAlgHom := GradedAlgHom.includeRight S 𝒜
  map_d' a := by simp
  map_curvature' := rfl

@[simp]
theorem includeRight_apply (hA : IsCurvedDGAlgebra 𝒜 dA wA) (a : A) :
    includeRight S hA a = 1 ⊗ₜ[R] a := (rfl)

variable {S} [Ring B] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
  {ℬ : ℤ → Submodule S B} [GradedAlgebra ℬ] {dB : B →ₗ[S] B} {wB : B}
  (hA : IsCurvedDGAlgebra 𝒜 dA wA) (hB : IsCurvedDGAlgebra ℬ dB wB)

/-- **The base change–restriction adjunction.** Strict curved `R`-morphisms from `A` to the
restriction of a curved differential graded `S`-algebra `B` correspond to strict curved
`S`-morphisms from the base change `S ⊗[R] A` to `B`, by `f ↦ (s ⊗ a ↦ s • f a)`. -/
def liftEquiv :
    CurvedDGAlgHom hA (hB.restrictScalars R) ≃ CurvedDGAlgHom (hA.baseChange S) hB where
  toFun f :=
    { toGradedAlgHom := GradedAlgHom.liftEquiv 𝒜 ℬ f.toGradedAlgHom
      map_d' x := by
        induction x with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul s a =>
          have hf := f.map_d a
          rw [LinearMap.coe_restrictScalars] at hf
          simp [hf]
      map_curvature' := by simp }
  invFun f :=
    { toGradedAlgHom := (GradedAlgHom.liftEquiv 𝒜 ℬ).symm f.toGradedAlgHom
      map_d' a := by simp
      map_curvature' := by simp }
  left_inv f := toGradedAlgHom_injective <| (GradedAlgHom.liftEquiv 𝒜 ℬ).left_inv _
  right_inv f := toGradedAlgHom_injective <| (GradedAlgHom.liftEquiv 𝒜 ℬ).right_inv _

@[simp]
theorem liftEquiv_tmul (f : CurvedDGAlgHom hA (hB.restrictScalars R)) (s : S) (a : A) :
    liftEquiv hA hB f (s ⊗ₜ[R] a) = s • f a := (rfl)

@[simp]
theorem liftEquiv_symm_apply (f : CurvedDGAlgHom (hA.baseChange S) hB) (a : A) :
    (liftEquiv hA hB).symm f a = f (1 ⊗ₜ[R] a) := (rfl)

variable {hB}

/-- Strict curved morphisms out of a base change are determined by their values on the elements
`1 ⊗ a`: this is the uniqueness half of the universal property of `CurvedDGAlgHom.liftEquiv`. -/
theorem baseChange_ext {f g : CurvedDGAlgHom (hA.baseChange S) hB}
    (h : ∀ a, f (1 ⊗ₜ[R] a) = g (1 ⊗ₜ[R] a)) : f = g :=
  (liftEquiv hA hB).symm.injective <| ext fun a ↦ by simpa using h a

variable (S) {hA} {C : Type*} [Ring C] [Algebra R C] {𝒞 : ℤ → Submodule R C} [GradedAlgebra 𝒞]
  {dC : C →ₗ[R] C} {wC : C} {hC : IsCurvedDGAlgebra 𝒞 dC wC}

/-- The base change `s ⊗ a ↦ s ⊗ f a` of a strict curved morphism of curved differential graded
`R`-algebras is a strict curved morphism of their base changes to `S`. -/
def baseChange (f : CurvedDGAlgHom hA hC) : CurvedDGAlgHom (hA.baseChange S) (hC.baseChange S) :=
  liftEquiv hA (hC.baseChange S) ((includeRight S hC).comp f)

@[simp]
theorem baseChange_tmul (f : CurvedDGAlgHom hA hC) (s : S) (a : A) :
    baseChange S f (s ⊗ₜ[R] a) = s ⊗ₜ[R] f a := by
  simp [baseChange, smul_tmul']

/-- Base change preserves identities. -/
@[simp]
theorem baseChange_id (hA : IsCurvedDGAlgebra 𝒜 dA wA) :
    baseChange S (CurvedDGAlgHom.id hA) = CurvedDGAlgHom.id (hA.baseChange S) :=
  baseChange_ext hA fun a ↦ by simp

/-- Base change preserves composition. -/
@[simp]
theorem baseChange_comp {D : Type*} [Ring D] [Algebra R D] {𝒟 : ℤ → Submodule R D}
    [GradedAlgebra 𝒟] {dD : D →ₗ[R] D} {wD : D} {hD : IsCurvedDGAlgebra 𝒟 dD wD}
    (g : CurvedDGAlgHom hC hD) (f : CurvedDGAlgHom hA hC) :
    baseChange S (g.comp f) = (baseChange S g).comp (baseChange S f) :=
  baseChange_ext hA fun a ↦ by simp

end CurvedDGAlgHom

end TauCeti
