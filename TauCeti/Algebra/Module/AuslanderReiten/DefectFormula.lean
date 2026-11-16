/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.SnakeLemma
public import TauCeti.Algebra.Module.AuslanderReiten.HomCokernel
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

## Main definitions

* `LinearMap.contravariantDefect` and `LinearMap.covariantDefect`: the two defects.
* `Function.Exact.contravariantDefectEquivKer`: `δ^*(X) ≅ ker H(φ)`, from the snake lemma.
* `Function.Exact.dualContravariantDefectEquivCovariantDefect`: **Auslander's defect formula**
  `D δ^*(X) ≅ δ_*(D Tr X)`.

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

end Defect

end Function.Exact
