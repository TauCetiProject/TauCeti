/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SnakeLemma
public import TauCeti.Algebra.Module.AuslanderReiten.HomCokernel
public import TauCeti.Algebra.Module.AuslanderReiten.Morphism
public import TauCeti.Algebra.Module.LinearMap.Defs
public import TauCeti.Algebra.Module.Injective.Hom
public import TauCeti.LinearAlgebra.Exact

/-!
# Auslander's defect formula

Let `A` be an algebra over a commutative ring `k`, let `E` be an injective `k`-module, and write
`D = Hom_k(-, E)`. For an exact sequence `δ : 0 → M₁ → M₂ → M₃ → 0` of `A`-modules, with maps
`φ : M₁ → M₂` and `ψ : M₂ → M₃`, the **contravariant defect** at `X` and the **covariant
defect** at `Y` are the cokernels

* `δ^*(X) = coker (Hom_A(X, ψ) : Hom_A(X, M₂) → Hom_A(X, M₃))`,
* `δ_*(Y) = coker (Hom_A(φ, Y) : Hom_A(M₂, Y) → Hom_A(M₁, Y))`.

**Auslander's defect formula** says that for a module `X` with a projective presentation
`P₁ → P₀ → X → 0` by finitely generated projectives,
`D δ^*(X) ≅ δ_*(D Tr X)`, where `Tr X` is the transpose of the presentation.

We follow Krause's short proof. For a module `N`, let `H(N)` be the cokernel of
`Hom_A(P₀, N) → Hom_A(P₁, N)`. The presentation gives exact rows
`0 → Hom_A(X, N) → Hom_A(P₀, N) → Hom_A(P₁, N) → H(N) → 0`, and `δ` gives left exact columns,
right exact at `P₀` since `P₀` is projective. The snake lemma identifies `δ^*(X)` with the kernel
of `H(φ) : H(M₁) → H(M₂)` (`LinearMap.homCokernelMap`); only projectivity of `P₀` is used here.
As `E` is injective, `D` turns this kernel into the cokernel of `D H(φ)`
(`LinearMap.cokernelEquivDualKer`). Finally `D H(N) ≅ Hom_A(N, D Tr X)` naturally in `N`
(`LinearMap.auslanderReitenHomCokernelDualEquiv`), so the cokernel of `D H(φ)` is `δ_*(D Tr X)`.

No finiteness of `k` or `A`, and no minimality of the presentation, is needed. The snake lemma is
Mathlib's `SnakeLemma.δ'`, in its module form.

The formula is natural in the exact sequence. A morphism `(a₁, a₂, a₃)` of exact sequences induces
`δ^*(X) → δ'^*(X)` (postcomposition with `a₃`) and `δ'_*(Y) → δ_*(Y)` (precomposition with `a₁`),
and the defect formula carries the dual of the first to the second. Each step of the proof is
natural: the snake map, because a lift for `δ` composed with `a₂` and `a₁` is a lift for `δ'`, and
`D H(N) ≅ Hom_A(N, D Tr X)`, by `LinearMap.auslanderReitenHomCokernelDualEquiv_map`.

The formula is also natural in the presented module. A map `t : X → X'` lifted to the
presentations by `(t₀, t₁)` induces `δ^*(X') → δ^*(X)` (precomposition with `t`) and
`δ_*(D Tr X) → δ_*(D Tr X')` (postcomposition with `D Tr(t)`), and the defect formula carries the
dual of the first to the second: the snake map is natural because lifts for `X'` composed with
`(t₀, t₁)` are lifts for `X`, and `D H(N) ≅ Hom_A(N, D Tr X)` is natural in the presentation.

## Main definitions

* `LinearMap.contravariantDefect` and `LinearMap.covariantDefect`: the two defects.
* `Function.Exact.contravariantDefectEquivKer`: `δ^*(X) ≅ ker H(φ)`, from the snake lemma.
* `Function.Exact.dualContravariantDefectEquivCovariantDefect`: **Auslander's defect formula**
  `D δ^*(X) ≅ δ_*(D Tr X)`.
* `LinearMap.contravariantDefectMap` and `LinearMap.covariantDefectMap`: the maps of defects
  induced by a morphism of exact sequences, functorial in it (`_id`, `_comp`).
* `Function.Exact.contravariantDefectEquivKer_mk`: the snake map on representatives.
* `Function.Exact.dualContravariantDefectEquivCovariantDefect_naturality`: naturality of the
  defect formula in the exact sequence.
* `LinearMap.contravariantDefectComap`, `LinearMap.covariantDefectMapRight` and
  `LinearMap.homCokernelComap`: the maps induced by a map of presented modules.
* `Function.Exact.dualContravariantDefectEquivCovariantDefect_comap`: naturality of the defect
  formula in the presented module, from `Function.Exact.contravariantDefectEquivKer_comap` and
  `LinearMap.auslanderReitenHomCokernelDualEquiv_comap`.

## References

* H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl. **365** (2003),
  267–270.
* M. Auslander, *Functors determined by objects*, in: Representation Theory of Algebras
  (Philadelphia, 1976), Marcel Dekker (1978), 1–244, Theorem III.4.1.
-/

public section

namespace LinearMap

open TauCeti Function

universe w

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

/-- The map `δ_*(Y) → δ_*(Y')` of covariant defects induced by `g : Y → Y'`: postcomposition
with `g`. -/
noncomputable def covariantDefectMapRight {M₁ M₂ Y Y' : Type*} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup Y] [Module A Y] [Module k Y]
    [IsScalarTower k A Y] [AddCommGroup Y'] [Module A Y'] [Module k Y'] [IsScalarTower k A Y']
    (φ : M₁ →ₗ[A] M₂) (g : Y →ₗ[A] Y') : covariantDefect k φ Y →ₗ[k] covariantDefect k φ Y' :=
  Submodule.mapQ _ _ (g.compRight k) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨g ∘ₗ u, rfl⟩)

@[simp]
theorem covariantDefectMapRight_mk {M₁ M₂ Y Y' : Type*} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup Y] [Module A Y] [Module k Y]
    [IsScalarTower k A Y] [AddCommGroup Y'] [Module A Y'] [Module k Y'] [IsScalarTower k A Y']
    (φ : M₁ →ₗ[A] M₂) (g : Y →ₗ[A] Y') (u : M₁ →ₗ[A] Y) :
    covariantDefectMapRight k φ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk (g ∘ₗ u) := by
  simp [covariantDefectMapRight]

@[simp]
theorem covariantDefectMapRight_id {M₁ M₂ Y : Type*} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup Y] [Module A Y] [Module k Y]
    [IsScalarTower k A Y] (φ : M₁ →ₗ[A] M₂) :
    covariantDefectMapRight k φ (LinearMap.id : Y →ₗ[A] Y) = LinearMap.id := by
  ext u
  simp

/-- The maps of covariant defects compose along composed maps. -/
theorem covariantDefectMapRight_comp {M₁ M₂ Y Y' Y'' : Type*} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup Y] [Module A Y] [Module k Y]
    [IsScalarTower k A Y] [AddCommGroup Y'] [Module A Y'] [Module k Y'] [IsScalarTower k A Y']
    [AddCommGroup Y''] [Module A Y''] [Module k Y''] [IsScalarTower k A Y''] (φ : M₁ →ₗ[A] M₂)
    (g : Y →ₗ[A] Y') (g' : Y' →ₗ[A] Y'') :
    covariantDefectMapRight k φ (g' ∘ₗ g) =
      covariantDefectMapRight k φ g' ∘ₗ covariantDefectMapRight k φ g := by
  ext u
  simp [LinearMap.comp_assoc]

/-- The map `H'(N) → H(N)` of Hom cokernels induced by a commutative square `t₀ ∘ f = f' ∘ t₁`
between presentations: precomposition with `t₁`. -/
noncomputable def homCokernelComap {P₀ P₁ P₀' P₁' : Type*} [AddCommGroup P₀] [Module A P₀]
    [AddCommGroup P₁] [Module A P₁] [AddCommGroup P₀'] [Module A P₀'] [AddCommGroup P₁']
    [Module A P₁'] {f : P₁ →ₗ[A] P₀} {f' : P₁' →ₗ[A] P₀'} {t₀ : P₀ →ₗ[A] P₀'}
    {t₁ : P₁ →ₗ[A] P₁'} (ht : t₀ ∘ₗ f = f' ∘ₗ t₁) (N : Type*) [AddCommGroup N] [Module A N]
    [Module k N] [IsScalarTower k A N] :
    ((P₁' →ₗ[A] N) ⧸ range (f'.lcomp k N)) →ₗ[k] ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) :=
  Submodule.mapQ _ _ (t₁.lcomp k N) (by
    rintro _ ⟨G, rfl⟩
    refine ⟨G ∘ₗ t₀, ?_⟩
    simp only [lcomp_apply']
    rw [LinearMap.comp_assoc, ht, ← LinearMap.comp_assoc])

@[simp]
theorem homCokernelComap_mk {P₀ P₁ P₀' P₁' : Type*} [AddCommGroup P₀] [Module A P₀]
    [AddCommGroup P₁] [Module A P₁] [AddCommGroup P₀'] [Module A P₀'] [AddCommGroup P₁']
    [Module A P₁'] {f : P₁ →ₗ[A] P₀} {f' : P₁' →ₗ[A] P₀'} {t₀ : P₀ →ₗ[A] P₀'}
    {t₁ : P₁ →ₗ[A] P₁'} (ht : t₀ ∘ₗ f = f' ∘ₗ t₁) {N : Type*} [AddCommGroup N] [Module A N]
    [Module k N] [IsScalarTower k A N] (G : P₁' →ₗ[A] N) :
    homCokernelComap k ht N (Submodule.Quotient.mk G) = Submodule.Quotient.mk (G ∘ₗ t₁) := by
  simp [homCokernelComap, lcomp_apply']

@[simp]
theorem homCokernelComap_id {P₀ P₁ : Type*} [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁]
    [Module A P₁] {f : P₁ →ₗ[A] P₀} (ht : LinearMap.id ∘ₗ f = f ∘ₗ LinearMap.id) (N : Type*)
    [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N] :
    homCokernelComap k ht N = LinearMap.id := by
  ext G
  simp

/-- The maps of Hom cokernels compose, in the reverse order, along composed squares. -/
theorem homCokernelComap_comp {P₀ P₁ P₀' P₁' P₀'' P₁'' : Type*} [AddCommGroup P₀] [Module A P₀]
    [AddCommGroup P₁] [Module A P₁] [AddCommGroup P₀'] [Module A P₀'] [AddCommGroup P₁']
    [Module A P₁'] [AddCommGroup P₀''] [Module A P₀''] [AddCommGroup P₁''] [Module A P₁'']
    {f : P₁ →ₗ[A] P₀} {f' : P₁' →ₗ[A] P₀'} {f'' : P₁'' →ₗ[A] P₀''} {t₀ : P₀ →ₗ[A] P₀'}
    {t₁ : P₁ →ₗ[A] P₁'} {t₀' : P₀' →ₗ[A] P₀''} {t₁' : P₁' →ₗ[A] P₁''}
    (ht : t₀ ∘ₗ f = f' ∘ₗ t₁) (ht' : t₀' ∘ₗ f' = f'' ∘ₗ t₁')
    (ht'' : (t₀' ∘ₗ t₀) ∘ₗ f = f'' ∘ₗ (t₁' ∘ₗ t₁)) (N : Type*) [AddCommGroup N] [Module A N]
    [Module k N] [IsScalarTower k A N] :
    homCokernelComap k ht'' N = homCokernelComap k ht N ∘ₗ homCokernelComap k ht' N := by
  ext G
  simp [LinearMap.comp_assoc]

/-- **Naturality of `D H(N) ≅ Hom_A(N, D Tr f)` in the presentation.** For a commutative square
`t₀ ∘ f = f' ∘ t₁`, precomposition with the map of Hom cokernels corresponds to postcomposition
with the dual `D Tr(t) : D Tr f → D Tr f'` of the map of transposes. -/
theorem auslanderReitenHomCokernelDualEquiv_comap {P₀ P₁ P₀' P₁' N : Type*} [AddCommGroup P₀]
    [Module A P₀] [Module.Finite A P₀] [Module.Projective A P₀] [AddCommGroup P₁] [Module A P₁]
    [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₀'] [Module A P₀']
    [Module.Finite A P₀'] [Module.Projective A P₀'] [AddCommGroup P₁'] [Module A P₁']
    [Module.Finite A P₁'] [Module.Projective A P₁'] [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] {E : Type*} [AddCommGroup E] [Module k E] {f : P₁ →ₗ[A] P₀}
    {f' : P₁' →ₗ[A] P₀'} {t₀ : P₀ →ₗ[A] P₀'} {t₁ : P₁ →ₗ[A] P₁'} (ht : t₀ ∘ₗ f = f' ∘ₗ t₁)
    (u : ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k] E) :
    auslanderReitenHomCokernelDualEquiv f' (u ∘ₗ homCokernelComap k ht N) =
      MatlisDual.mapOp (AuslanderReitenTranspose.map t₀ t₁ ht) ∘ₗ
        auslanderReitenHomCokernelDualEquiv f u := by
  ext n : 1
  apply (MatlisDual.equivLinearMap k E _).injective
  ext τ
  obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective f' τ
  simp only [auslanderReitenHomCokernelDualEquiv_apply_mk, LinearMap.comp_apply,
    homCokernelComap_mk, MatlisDual.mapOp_apply, AuslanderReitenTranspose.map_mk]
  congr 2
  ext x
  simp [balancedDualTensorHom_tmul]

end PresentationMaps

end LinearMap

namespace Function.Exact

open LinearMap TauCeti

section Defect

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
  {P₀ P₁ X : Type*} [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup X] [Module A X]
  {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module A M₁] [Module k M₁] [IsScalarTower k A M₁]
  [AddCommGroup M₂] [Module A M₂] [Module k M₂] [IsScalarTower k A M₂]
  [AddCommGroup M₃] [Module A M₃] [Module k M₃] [IsScalarTower k A M₃]

variable [Module.Projective A P₀]

/-- **The snake lemma for the defect.** For a cokernel presentation `P₁ → P₀ → X → 0` with `P₀`
projective and an exact sequence `0 → M₁ → M₂ → M₃ → 0`, the contravariant defect `δ^*(X)` is
the kernel of `H(φ) : H(M₁) → H(M₂)`. -/
noncomputable def contravariantDefectEquivKer {f : P₁ →ₗ[A] P₀} {p : P₀ →ₗ[A] X}
    (hfp : Exact f p) (hp : Surjective p) {φ : M₁ →ₗ[A] M₂} {ψ : M₂ →ₗ[A] M₃}
    (hφ : Injective φ) (hψ : Surjective ψ) (hφψ : Exact φ ψ) :
    contravariantDefect k ψ X ≃ₗ[k] ker (homCokernelMap k f φ) :=
  let δ := SnakeLemma.δ' (f.lcomp k M₁) (f.lcomp k M₂) (f.lcomp k M₃)
    (φ.compRight k) (ψ.compRight k) (hφψ.compRight_of_injective (T := k) P₀ hφ)
    (φ.compRight k) (ψ.compRight k) (hφψ.compRight_of_injective (T := k) P₁ hφ) rfl rfl
    (p.lcomp k M₃) (hfp.lcomp_of_surjective (T := k) M₃ hp) (range (f.lcomp k M₁)).mkQ
    (exact_map_mkQ_range _)
    (fun g ↦ Module.projective_lifting_property ψ g hψ)
    (fun _ _ hgh ↦ LinearMap.ext fun x ↦ hφ (LinearMap.congr_fun hgh x))
  have h₁ : Exact (ψ.compRight k : (X →ₗ[A] M₂) →ₗ[k] (X →ₗ[A] M₃)) δ :=
    SnakeLemma.exact_δ'_right _ _ _ _ _ _ _ _ _ _ _ (p.lcomp k M₂)
      (hfp.lcomp_of_surjective (T := k) M₂ hp) _ _ _ _ _ _ _ rfl
      (lcomp_injective_of_surjective p hp)
  have h₂ : Exact δ (homCokernelMap k f φ) :=
    SnakeLemma.exact_δ'_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (range (f.lcomp k M₂)).mkQ
      (exact_map_mkQ_range _) _ _ _ (homCokernelMap_comp_mkQ k f φ) (Submodule.mkQ_surjective _)
  Submodule.quotEquivOfEq _ _ h₁.linearMap_ker_eq.symm ≪≫ₗ δ.quotKerEquivRange ≪≫ₗ
    LinearEquiv.ofEq _ _ h₂.linearMap_ker_eq.symm

variable {f : P₁ →ₗ[A] P₀} {p : P₀ →ₗ[A] X} {φ : M₁ →ₗ[A] M₂} {ψ : M₂ →ₗ[A] M₃}

/-- **The snake map on representatives.** If `y : P₀ → M₂` lifts `g ∘ p` along `ψ` and
`z : P₁ → M₁` lifts `y ∘ f` along `φ`, then `δ^*(X) ≅ ker H(φ)` sends the class of `g` to the
class of `z`. -/
theorem contravariantDefectEquivKer_mk (hfp : Exact f p) (hp : Surjective p) (hφ : Injective φ)
    (hψ : Surjective ψ) (hφψ : Exact φ ψ) (g : X →ₗ[A] M₃) (y : P₀ →ₗ[A] M₂)
    (hy : ψ ∘ₗ y = g ∘ₗ p) (z : P₁ →ₗ[A] M₁) (hz : φ ∘ₗ z = y ∘ₗ f) :
    (contravariantDefectEquivKer (k := k) hfp hp hφ hψ hφψ (Submodule.Quotient.mk g) :
      (P₁ →ₗ[A] M₁) ⧸ range (f.lcomp k M₁)) = Submodule.Quotient.mk z := by
  simp only [contravariantDefectEquivKer, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearEquiv.coe_ofEq_apply, LinearMap.quotKerEquivRange_apply_mk]
  exact SnakeLemma.δ'_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g y
    (by rw [compRight_apply, lcomp_apply']; exact hy) z
    (by rw [compRight_apply, lcomp_apply']; exact hz)

variable {M₁' M₂' M₃' : Type*}
  [AddCommGroup M₁'] [Module A M₁'] [Module k M₁'] [IsScalarTower k A M₁']
  [AddCommGroup M₂'] [Module A M₂'] [Module k M₂'] [IsScalarTower k A M₂']
  [AddCommGroup M₃'] [Module A M₃'] [Module k M₃'] [IsScalarTower k A M₃']
  {φ' : M₁' →ₗ[A] M₂'} {ψ' : M₂' →ₗ[A] M₃'} {a₁ : M₁ →ₗ[A] M₁'} {a₂ : M₂ →ₗ[A] M₂'}
  {a₃ : M₃ →ₗ[A] M₃'}

/-- **Naturality of the snake lemma for the defect.** A morphism `(a₁, a₂, a₃)` of exact sequences
`0 → M₁ → M₂ → M₃ → 0` carries `δ^*(X) ≅ ker H(φ)` to `δ'^*(X) ≅ ker H(φ')`: postcomposition
with `a₃` on the left corresponds to `H(a₁)` on the right. -/
theorem contravariantDefectEquivKer_naturality (hfp : Exact f p) (hp : Surjective p)
    (hφ : Injective φ) (hψ : Surjective ψ) (hφψ : Exact φ ψ) (hφ' : Injective φ')
    (hψ' : Surjective ψ') (hφψ' : Exact φ' ψ') (h₁ : a₂ ∘ₗ φ = φ' ∘ₗ a₁)
    (h₂ : a₃ ∘ₗ ψ = ψ' ∘ₗ a₂) (x : contravariantDefect k ψ X) :
    (contravariantDefectEquivKer hfp hp hφ' hψ' hφψ' (contravariantDefectMap k h₂ X x) :
      (P₁ →ₗ[A] M₁') ⧸ range (f.lcomp k M₁')) =
      homCokernelMap k f a₁ (contravariantDefectEquivKer hfp hp hφ hψ hφψ x) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, hy⟩ := Module.projective_lifting_property ψ (g ∘ₗ p) hψ
  obtain ⟨z, hz⟩ := (hφψ.compRight_of_injective (T := k) P₁ hφ (y ∘ₗ f)).mp (by
    rw [compRight_apply, ← LinearMap.comp_assoc, hy, LinearMap.comp_assoc,
      hfp.linearMap_comp_eq_zero, LinearMap.comp_zero])
  rw [compRight_apply] at hz
  rw [contravariantDefectMap_mk, contravariantDefectEquivKer_mk hfp hp hφ hψ hφψ g y hy z hz,
    contravariantDefectEquivKer_mk hfp hp hφ' hψ' hφψ' (a₃ ∘ₗ g) (a₂ ∘ₗ y)
      (comp_comp_eq_comp_comp_of_comp_eq h₂ hy) (a₁ ∘ₗ z)
      (comp_comp_eq_comp_comp_of_comp_eq h₁ hz), homCokernelMap_mk]

variable {P₀' P₁' X' : Type*} [AddCommGroup P₀'] [Module A P₀'] [Module.Projective A P₀']
  [AddCommGroup P₁'] [Module A P₁'] [AddCommGroup X'] [Module A X'] {f' : P₁' →ₗ[A] P₀'}
  {p' : P₀' →ₗ[A] X'} {t : X →ₗ[A] X'} {t₀ : P₀ →ₗ[A] P₀'} {t₁ : P₁ →ₗ[A] P₁'}

/-- **Naturality of the snake lemma for the defect in the presented module.** For a map
`t : X → X'` lifted to presentations by `(t₀, t₁)`, precomposition with `t` on `δ^*` corresponds to
the map of Hom cokernels induced by the lift. -/
theorem contravariantDefectEquivKer_comap (hfp : Exact f p) (hp : Surjective p)
    (hfp' : Exact f' p') (hp' : Surjective p') (hφ : Injective φ) (hψ : Surjective ψ)
    (hφψ : Exact φ ψ) (ht₀ : p' ∘ₗ t₀ = t ∘ₗ p) (ht₁ : t₀ ∘ₗ f = f' ∘ₗ t₁)
    (x : contravariantDefect k ψ X') :
    (contravariantDefectEquivKer hfp hp hφ hψ hφψ (contravariantDefectComap k ψ t x) :
      (P₁ →ₗ[A] M₁) ⧸ range (f.lcomp k M₁)) =
      homCokernelComap k ht₁ M₁ (contravariantDefectEquivKer hfp' hp' hφ hψ hφψ x) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, hy⟩ := Module.projective_lifting_property ψ (g ∘ₗ p') hψ
  obtain ⟨z, hz⟩ := (hφψ.compRight_of_injective (T := k) P₁' hφ (y ∘ₗ f')).mp (by
    rw [compRight_apply, ← LinearMap.comp_assoc, hy, LinearMap.comp_assoc,
      hfp'.linearMap_comp_eq_zero, LinearMap.comp_zero])
  rw [compRight_apply] at hz
  rw [contravariantDefectComap_mk, contravariantDefectEquivKer_mk hfp' hp' hφ hψ hφψ g y hy z hz,
    contravariantDefectEquivKer_mk hfp hp hφ hψ hφψ (g ∘ₗ t) (y ∘ₗ t₀)
      (by rw [← LinearMap.comp_assoc, hy, LinearMap.comp_assoc, ht₀, ← LinearMap.comp_assoc])
      (z ∘ₗ t₁)
      (by rw [← LinearMap.comp_assoc, hz, LinearMap.comp_assoc, ← ht₁, ← LinearMap.comp_assoc]),
    homCokernelComap_mk]

variable [Module.Finite A P₀] [Module.Finite A P₁] [Module.Projective A P₁]
  {E : Type w} [AddCommGroup E] [Module k E] [Small.{w} k] [Module.Injective k E]

/-- **Auslander's defect formula.** Let `A` be a `k`-algebra, `E` an injective `k`-module and
`D = Hom_k(-, E)`. For an exact sequence `0 → M₁ → M₂ → M₃ → 0` of `A`-modules and a module `X`
with a presentation `P₁ → P₀ → X → 0` by finitely generated projectives,
`D δ^*(X) ≅ δ_*(D Tr X)`, where `Tr X` is the transpose of the presentation. -/
noncomputable def dualContravariantDefectEquivCovariantDefect {f : P₁ →ₗ[A] P₀} {p : P₀ →ₗ[A] X}
    (hfp : Exact f p) (hp : Surjective p) {φ : M₁ →ₗ[A] M₂} {ψ : M₂ →ₗ[A] M₃} (hφ : Injective φ)
    (hψ : Surjective ψ) (hφψ : Exact φ ψ) :
    (contravariantDefect k ψ X →ₗ[k] E) ≃ₗ[k]
      covariantDefect k φ (MatlisDual k E (AuslanderReitenTranspose f)) :=
  LinearEquiv.arrowCongr (contravariantDefectEquivKer hfp hp hφ hψ hφψ) (LinearEquiv.refl k E) ≪≫ₗ
    (cokernelEquivDualKer (homCokernelMap k f φ)).symm ≪≫ₗ
      Submodule.Quotient.equiv _ _ (auslanderReitenHomCokernelDualEquiv f) (by
        ext g
        simp only [Submodule.mem_map, mem_range, lcomp_apply']
        constructor
        · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
          exact ⟨auslanderReitenHomCokernelDualEquiv f u,
            (auslanderReitenHomCokernelDualEquiv_map f φ u).symm⟩
        · rintro ⟨v, rfl⟩
          obtain ⟨u, rfl⟩ := (auslanderReitenHomCokernelDualEquiv f).surjective v
          exact ⟨_, ⟨u, rfl⟩, auslanderReitenHomCokernelDualEquiv_map f φ u⟩)

/-- Transport of functionals along `cokernelEquivDualKer`: if `κ₂ ∘ c = h ∘ κ₁` on the kernels
and `v` represents the functional `χ` through `κ₂`, then `v ∘ h` represents `χ ∘ c` through `κ₁`. -/
private theorem cokernelEquivDualKer_symm_arrowCongr_comp {D₁ D₂ H₁ H₂ G₁ G₂ : Type*}
    [AddCommGroup D₁] [Module k D₁] [AddCommGroup D₂] [Module k D₂] [AddCommGroup H₁]
    [Module k H₁] [AddCommGroup H₂] [Module k H₂] [AddCommGroup G₁] [Module k G₁]
    [AddCommGroup G₂] [Module k G₂] {g₁ : H₁ →ₗ[k] G₁} {g₂ : H₂ →ₗ[k] G₂}
    (κ₁ : D₁ ≃ₗ[k] ker g₁) (κ₂ : D₂ ≃ₗ[k] ker g₂) {c : D₁ →ₗ[k] D₂} {h : H₁ →ₗ[k] H₂}
    (hc : ∀ x, (κ₂ (c x) : H₂) = h (κ₁ x)) {χ : D₂ →ₗ[k] E} {v : H₂ →ₗ[k] E}
    (hv : Submodule.Quotient.mk v =
      (cokernelEquivDualKer (S := k) g₂).symm (κ₂.arrowCongr (LinearEquiv.refl k E) χ)) :
    (cokernelEquivDualKer (S := k) g₁).symm (κ₁.arrowCongr (LinearEquiv.refl k E) (χ ∘ₗ c)) =
      Submodule.Quotient.mk (v ∘ₗ h) := by
  rw [LinearEquiv.symm_apply_eq, cokernelEquivDualKer_mk]
  ext u
  obtain ⟨x, rfl⟩ := κ₁.surjective u
  have hv' := LinearMap.congr_fun (congrArg (cokernelEquivDualKer (S := k) g₂) hv) (κ₂ (c x))
  rw [cokernelEquivDualKer_mk, LinearEquiv.apply_symm_apply] at hv'
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.arrowCongr_apply,
    LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply] at hv' ⊢
  rw [← hc, hv']

/-- **Naturality of Auslander's defect formula** in the exact sequence. For a morphism
`(a₁, a₂, a₃)` from `0 → M₁ → M₂ → M₃ → 0` to `0 → M₁' → M₂' → M₃' → 0`, the isomorphisms
`D δ^*(X) ≅ δ_*(D Tr X)` and `D δ'^*(X) ≅ δ'_*(D Tr X)` commute with the dual of postcomposition
by `a₃` and with precomposition by `a₁`. -/
theorem dualContravariantDefectEquivCovariantDefect_naturality (hfp : Exact f p)
    (hp : Surjective p) (hφ : Injective φ) (hψ : Surjective ψ) (hφψ : Exact φ ψ)
    (hφ' : Injective φ') (hψ' : Surjective ψ') (hφψ' : Exact φ' ψ') (h₁ : a₂ ∘ₗ φ = φ' ∘ₗ a₁)
    (h₂ : a₃ ∘ₗ ψ = ψ' ∘ₗ a₂) (χ : contravariantDefect k ψ' X →ₗ[k] E) :
    dualContravariantDefectEquivCovariantDefect hfp hp hφ hψ hφψ
        (χ ∘ₗ contravariantDefectMap k h₂ X) =
      covariantDefectMap k h₁ _
        (dualContravariantDefectEquivCovariantDefect hfp hp hφ' hψ' hφψ' χ) := by
  simp only [dualContravariantDefectEquivCovariantDefect, LinearEquiv.trans_apply]
  -- Represent the class attached to `χ` by a functional `v` on `H(M₁')`.
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _
    ((cokernelEquivDualKer (S := k) (homCokernelMap k f φ')).symm
      ((contravariantDefectEquivKer hfp hp hφ' hψ' hφψ').arrowCongr (LinearEquiv.refl k E) χ))
  rw [cokernelEquivDualKer_symm_arrowCongr_comp _ _
    (contravariantDefectEquivKer_naturality hfp hp hφ hψ hφψ hφ' hψ' hφψ' h₁ h₂) hv, ← hv]
  simp [Submodule.Quotient.equiv_apply]

variable [Module.Finite A P₀'] [Module.Finite A P₁'] [Module.Projective A P₁']

/-- **Naturality of Auslander's defect formula in the presented module.** For a map `t : X → X'`
lifted by `(t₀, t₁)` to the presentations, the isomorphisms `D δ^*(X) ≅ δ_*(D Tr X)` and
`D δ^*(X') ≅ δ_*(D Tr X')` carry the dual of precomposition with `t` to postcomposition with the
dual `D Tr(t) : D Tr X → D Tr X'` of the map of transposes. -/
theorem dualContravariantDefectEquivCovariantDefect_comap (hfp : Exact f p) (hp : Surjective p)
    (hfp' : Exact f' p') (hp' : Surjective p') (hφ : Injective φ) (hψ : Surjective ψ)
    (hφψ : Exact φ ψ) (ht₀ : p' ∘ₗ t₀ = t ∘ₗ p) (ht₁ : t₀ ∘ₗ f = f' ∘ₗ t₁)
    (χ : contravariantDefect k ψ X →ₗ[k] E) :
    dualContravariantDefectEquivCovariantDefect hfp' hp' hφ hψ hφψ
        (χ ∘ₗ contravariantDefectComap k ψ t) =
      covariantDefectMapRight k φ (MatlisDual.mapOp (AuslanderReitenTranspose.map t₀ t₁ ht₁))
        (dualContravariantDefectEquivCovariantDefect hfp hp hφ hψ hφψ χ) := by
  simp only [dualContravariantDefectEquivCovariantDefect, LinearEquiv.trans_apply]
  -- Represent the class attached to `χ` by a functional `v` on `H(M₁)`.
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _
    ((cokernelEquivDualKer (S := k) (homCokernelMap k f φ)).symm
      ((contravariantDefectEquivKer hfp hp hφ hψ hφψ).arrowCongr (LinearEquiv.refl k E) χ))
  rw [cokernelEquivDualKer_symm_arrowCongr_comp _ _
    (contravariantDefectEquivKer_comap hfp hp hfp' hp' hφ hψ hφψ ht₀ ht₁) hv, ← hv]
  simp [Submodule.Quotient.equiv_apply, auslanderReitenHomCokernelDualEquiv_comap]

end Defect

end Function.Exact
