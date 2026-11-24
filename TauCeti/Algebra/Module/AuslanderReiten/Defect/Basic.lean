/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The defects of a map of modules

Let `A` be an algebra over a commutative ring `k`. For `A`-linear maps `φ : M₁ → M₂` and
`ψ : M₂ → M₃`, the **contravariant defect** of `ψ` at `X` and the **covariant defect** of `φ` at
`Y` are the cokernels

* `δ^*(X) = coker (Hom_A(X, ψ) : Hom_A(X, M₂) → Hom_A(X, M₃))`,
* `δ_*(Y) = coker (Hom_A(φ, Y) : Hom_A(M₂, Y) → Hom_A(M₁, Y))`,

as `k`-modules. They are functorial in commutative squares and in the test modules `X` and `Y`.
For an exact sequence `0 → M₁ → M₂ → M₃ → 0` they are related by Auslander's defect formula
(`TauCeti/Algebra/Module/AuslanderReiten/Defect/Formula.lean`).

## Main definitions

* `LinearMap.contravariantDefect` and `LinearMap.covariantDefect`: the two defects.
* `LinearMap.contravariantDefectMap` and `LinearMap.covariantDefectMap`: the maps of defects
  induced by a commutative square, functorial in it (`_id`, `_comp`).
* `LinearMap.contravariantDefectComap`: the map of contravariant defects induced by a map of test
  modules.

## References

* M. Auslander, *Functors and morphisms determined by objects*, in: Representation Theory of
  Algebras (Philadelphia, 1976), Marcel Dekker (1978), 1–244.
-/

public section

namespace LinearMap

section Defects

variable (k : Type*) {A : Type*} [CommRing k] [Ring A] [Algebra k A]
  {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module A M₁] [Module k M₁] [IsScalarTower k A M₁]
  [AddCommGroup M₂] [Module A M₂] [Module k M₂] [IsScalarTower k A M₂]
  [AddCommGroup M₃] [Module A M₃] [Module k M₃] [IsScalarTower k A M₃]

/-- The **contravariant defect** `δ^*(X)` of `ψ : M₂ → M₃` at `X`: the cokernel of
`Hom_A(X, ψ) : Hom_A(X, M₂) → Hom_A(X, M₃)`. -/
abbrev contravariantDefect (ψ : M₂ →ₗ[A] M₃) (X : Type*) [AddCommGroup X] [Module A X] :
    Type _ :=
  (X →ₗ[A] M₃) ⧸ range (ψ.compRight k : (X →ₗ[A] M₂) →ₗ[k] (X →ₗ[A] M₃))

/-- The **covariant defect** `δ_*(Y)` of `φ : M₁ → M₂` at `Y`: the cokernel of
`Hom_A(φ, Y) : Hom_A(M₂, Y) → Hom_A(M₁, Y)`. -/
abbrev covariantDefect (φ : M₁ →ₗ[A] M₂) (Y : Type*) [AddCommGroup Y] [Module A Y] [Module k Y]
    [IsScalarTower k A Y] : Type _ :=
  (M₁ →ₗ[A] Y) ⧸ range (φ.lcomp k Y)

end Defects

section DefectMaps

variable (k : Type*) {A : Type*} [CommRing k] [Ring A] [Algebra k A]
  {M₁ M₂ M₃ M₁' M₂' M₃' : Type*} [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃] [AddCommGroup M₁'] [Module A M₁'] [AddCommGroup M₂']
  [Module A M₂'] [AddCommGroup M₃'] [Module A M₃']

section Contravariant

variable [Module k M₂] [IsScalarTower k A M₂] [Module k M₃] [IsScalarTower k A M₃]
  [Module k M₂'] [IsScalarTower k A M₂'] [Module k M₃'] [IsScalarTower k A M₃']

/-- The map `δ^*(X) → δ'^*(X)` of contravariant defects induced by a commutative square
`a₃ ∘ ψ = ψ' ∘ a₂`: postcomposition with `a₃`. -/
noncomputable def contravariantDefectMap {ψ : M₂ →ₗ[A] M₃} {ψ' : M₂' →ₗ[A] M₃'}
    {a₂ : M₂ →ₗ[A] M₂'} {a₃ : M₃ →ₗ[A] M₃'} (h : a₃ ∘ₗ ψ = ψ' ∘ₗ a₂)
    (X : Type*) [AddCommGroup X] [Module A X] :
    contravariantDefect k ψ X →ₗ[k] contravariantDefect k ψ' X :=
  Submodule.mapQ _ _ (a₃.compRight k) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨a₂ ∘ₗ g, LinearMap.ext fun x ↦ by simpa using (LinearMap.congr_fun h (g x)).symm⟩)

@[simp]
theorem contravariantDefectMap_mk {ψ : M₂ →ₗ[A] M₃} {ψ' : M₂' →ₗ[A] M₃'}
    {a₂ : M₂ →ₗ[A] M₂'} {a₃ : M₃ →ₗ[A] M₃'} (h : a₃ ∘ₗ ψ = ψ' ∘ₗ a₂)
    {X : Type*} [AddCommGroup X] [Module A X] (g : X →ₗ[A] M₃) :
    contravariantDefectMap k h X (Submodule.Quotient.mk g) = Submodule.Quotient.mk (a₃ ∘ₗ g) := by
  simp [contravariantDefectMap]

@[simp]
theorem contravariantDefectMap_id {ψ : M₂ →ₗ[A] M₃} (h : LinearMap.id ∘ₗ ψ = ψ ∘ₗ LinearMap.id)
    (X : Type*) [AddCommGroup X] [Module A X] :
    contravariantDefectMap k h X = LinearMap.id := by
  ext g
  simp

variable {M₂'' M₃'' : Type*} [AddCommGroup M₂''] [Module A M₂''] [Module k M₂'']
  [IsScalarTower k A M₂''] [AddCommGroup M₃''] [Module A M₃''] [Module k M₃'']
  [IsScalarTower k A M₃''] in
/-- The maps of contravariant defects compose along composed squares. -/
theorem contravariantDefectMap_comp {ψ : M₂ →ₗ[A] M₃} {ψ' : M₂' →ₗ[A] M₃'}
    {ψ'' : M₂'' →ₗ[A] M₃''} {a₂ : M₂ →ₗ[A] M₂'} {a₃ : M₃ →ₗ[A] M₃'} {b₂ : M₂' →ₗ[A] M₂''}
    {b₃ : M₃' →ₗ[A] M₃''} (h : a₃ ∘ₗ ψ = ψ' ∘ₗ a₂) (h' : b₃ ∘ₗ ψ' = ψ'' ∘ₗ b₂)
    (h'' : (b₃ ∘ₗ a₃) ∘ₗ ψ = ψ'' ∘ₗ (b₂ ∘ₗ a₂)) (X : Type*) [AddCommGroup X] [Module A X] :
    contravariantDefectMap k h'' X =
      contravariantDefectMap k h' X ∘ₗ contravariantDefectMap k h X := by
  ext g
  simp [LinearMap.comp_assoc]

end Contravariant

/-- The map `δ'_*(Y) → δ_*(Y)` of covariant defects induced by a commutative square
`a₂ ∘ φ = φ' ∘ a₁`: precomposition with `a₁`. -/
noncomputable def covariantDefectMap {φ : M₁ →ₗ[A] M₂} {φ' : M₁' →ₗ[A] M₂'}
    {a₁ : M₁ →ₗ[A] M₁'} {a₂ : M₂ →ₗ[A] M₂'} (h : a₂ ∘ₗ φ = φ' ∘ₗ a₁)
    (Y : Type*) [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y] :
    covariantDefect k φ' Y →ₗ[k] covariantDefect k φ Y :=
  Submodule.mapQ _ _ (a₁.lcomp k Y) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨g ∘ₗ a₂, LinearMap.ext fun x ↦ by simpa using congrArg g (LinearMap.congr_fun h x)⟩)

@[simp]
theorem covariantDefectMap_mk {φ : M₁ →ₗ[A] M₂} {φ' : M₁' →ₗ[A] M₂'}
    {a₁ : M₁ →ₗ[A] M₁'} {a₂ : M₂ →ₗ[A] M₂'} (h : a₂ ∘ₗ φ = φ' ∘ₗ a₁)
    {Y : Type*} [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y]
    (u : M₁' →ₗ[A] Y) :
    covariantDefectMap k h Y (Submodule.Quotient.mk u) = Submodule.Quotient.mk (u ∘ₗ a₁) := by
  simp [covariantDefectMap, lcomp_apply']

@[simp]
theorem covariantDefectMap_id {φ : M₁ →ₗ[A] M₂} (h : LinearMap.id ∘ₗ φ = φ ∘ₗ LinearMap.id)
    (Y : Type*) [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y] :
    covariantDefectMap k h Y = LinearMap.id := by
  ext u
  simp

variable {M₁'' M₂'' : Type*} [AddCommGroup M₁''] [Module A M₁''] [AddCommGroup M₂'']
  [Module A M₂''] in
/-- The maps of covariant defects compose, in the reverse order, along composed squares. -/
theorem covariantDefectMap_comp {φ : M₁ →ₗ[A] M₂} {φ' : M₁' →ₗ[A] M₂'} {φ'' : M₁'' →ₗ[A] M₂''}
    {a₁ : M₁ →ₗ[A] M₁'} {a₂ : M₂ →ₗ[A] M₂'} {b₁ : M₁' →ₗ[A] M₁''} {b₂ : M₂' →ₗ[A] M₂''}
    (h : a₂ ∘ₗ φ = φ' ∘ₗ a₁) (h' : b₂ ∘ₗ φ' = φ'' ∘ₗ b₁)
    (h'' : (b₂ ∘ₗ a₂) ∘ₗ φ = φ'' ∘ₗ (b₁ ∘ₗ a₁))
    (Y : Type*) [AddCommGroup Y] [Module A Y] [Module k Y] [IsScalarTower k A Y] :
    covariantDefectMap k h'' Y = covariantDefectMap k h Y ∘ₗ covariantDefectMap k h' Y := by
  ext u
  simp [LinearMap.comp_assoc]

end DefectMaps

section PresentationMaps

variable (k : Type*) {A : Type*} [CommRing k] [Ring A] [Algebra k A]

/-- The map `δ^*(X') → δ^*(X)` of contravariant defects induced by `t : X → X'`: precomposition
with `t`. -/
noncomputable def contravariantDefectComap {M₂ M₃ X X' : Type*} [AddCommGroup M₂] [Module A M₂]
    [Module k M₂] [IsScalarTower k A M₂] [AddCommGroup M₃] [Module A M₃] [Module k M₃]
    [IsScalarTower k A M₃] [AddCommGroup X] [Module A X] [AddCommGroup X'] [Module A X']
    (ψ : M₂ →ₗ[A] M₃) (t : X →ₗ[A] X') :
    contravariantDefect k ψ X' →ₗ[k] contravariantDefect k ψ X :=
  Submodule.mapQ _ _ (t.lcomp k M₃) (by
    rintro _ ⟨g, rfl⟩
    exact ⟨g ∘ₗ t, rfl⟩)

@[simp]
theorem contravariantDefectComap_mk {M₂ M₃ X X' : Type*} [AddCommGroup M₂] [Module A M₂]
    [Module k M₂] [IsScalarTower k A M₂] [AddCommGroup M₃] [Module A M₃] [Module k M₃]
    [IsScalarTower k A M₃] [AddCommGroup X] [Module A X] [AddCommGroup X'] [Module A X']
    (ψ : M₂ →ₗ[A] M₃) (t : X →ₗ[A] X') (g : X' →ₗ[A] M₃) :
    contravariantDefectComap k ψ t (Submodule.Quotient.mk g) = Submodule.Quotient.mk (g ∘ₗ t) := by
  simp [contravariantDefectComap, lcomp_apply']

@[simp]
theorem contravariantDefectComap_id {M₂ M₃ X : Type*} [AddCommGroup M₂] [Module A M₂]
    [Module k M₂] [IsScalarTower k A M₂] [AddCommGroup M₃] [Module A M₃] [Module k M₃]
    [IsScalarTower k A M₃] [AddCommGroup X] [Module A X] (ψ : M₂ →ₗ[A] M₃) :
    contravariantDefectComap k ψ (LinearMap.id : X →ₗ[A] X) = LinearMap.id := by
  ext g
  simp

/-- The maps of contravariant defects compose, in the reverse order, along composed maps. -/
theorem contravariantDefectComap_comp {M₂ M₃ X X' X'' : Type*} [AddCommGroup M₂] [Module A M₂]
    [Module k M₂] [IsScalarTower k A M₂] [AddCommGroup M₃] [Module A M₃] [Module k M₃]
    [IsScalarTower k A M₃] [AddCommGroup X] [Module A X] [AddCommGroup X'] [Module A X']
    [AddCommGroup X''] [Module A X''] (ψ : M₂ →ₗ[A] M₃) (t : X →ₗ[A] X') (t' : X' →ₗ[A] X'') :
    contravariantDefectComap k ψ (t' ∘ₗ t) =
      contravariantDefectComap k ψ t ∘ₗ contravariantDefectComap k ψ t' := by
  ext g
  simp [LinearMap.comp_assoc]

end PresentationMaps

end LinearMap
