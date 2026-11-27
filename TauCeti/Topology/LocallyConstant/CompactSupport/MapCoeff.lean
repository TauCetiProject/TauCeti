/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyConstant.CompactSupport

/-!
# Change of coefficients for locally constant functions with compact support

Let `X` be a topological space, `σ : A →+* B` a homomorphism of semirings and `φ : M → N` a
`σ`-semilinear map. Composing with `φ` sends a locally constant function `f : X → M` with compact
support to `φ ∘ f`, which again has compact support since `φ 0 = 0`. This is a `σ`-semilinear map
`C_c^∞(X, M) → C_c^∞(X, N)` (`LocallyConstant.compactlySupported.map`), functorial in `φ` and
sending the indicator `1_K • m` of a compact open set to `1_K • φ m`. Taking `φ = σ`, viewed as a
`σ`-semilinear map `A → B` (`RingHom.toSemilinearMap`), gives the change of coefficients
`C_c^∞(X, A) → C_c^∞(X, B)`.

## Main definitions

* `LocallyConstant.compactlySupported.map φ`: the pushforward `C_c^∞(X, M) → C_c^∞(X, N)`,
  `f ↦ φ ∘ f`, along a semilinear map `φ`.

## Main results

* `LocallyConstant.compactlySupported.map_compactOpenIndicator`: pushing `1_K • m` forward along
  `φ` gives `1_K • φ m`.
* `LocallyConstant.compactlySupported.map_id`, `LocallyConstant.compactlySupported.map_comp`:
  functoriality of the pushforward.
-/

public section

open TopologicalSpace

namespace LocallyConstant.compactlySupported

variable {X : Type*} [TopologicalSpace X] {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]

section Map

variable {M N : Type*} [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module B N]
  {σ : A →+* B}

/-- Pushforward of test functions along a `σ`-semilinear map `φ : M → N`: `f ↦ φ ∘ f`, a
`σ`-semilinear map `C_c^∞(X, M) → C_c^∞(X, N)`. -/
noncomputable def map (φ : M →ₛₗ[σ] N) :
    compactlySupported A X M →ₛₗ[σ] compactlySupported B X N where
  toFun f := ⟨(f : LocallyConstant X M).map φ, map_mem_compactlySupported f.property (map_zero φ)⟩
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

/-- The value of `φ ∘ f` at `x` is `φ (f x)`. -/
@[simp]
theorem map_apply (φ : M →ₛₗ[σ] N) (f : compactlySupported A X M) (x : X) :
    (map φ f : LocallyConstant X N) x = φ ((f : LocallyConstant X M) x) :=
  (rfl)

/-- Pushing the indicator `1_K • m` forward along `φ` gives the indicator `1_K • φ m`. -/
@[simp]
theorem map_compactOpenIndicator [T2Space X] (φ : M →ₛₗ[σ] N) (K : CompactOpens X) (m : M) :
    map φ ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ =
      ⟨compactOpenIndicator K (φ m), compactOpenIndicator_mem_compactlySupported K (φ m)⟩ :=
  Subtype.ext (LocallyConstant.map_compactOpenIndicator (map_zero φ) K m)

/-- Pushing forward along the identity does nothing. -/
@[simp]
theorem map_id (f : compactlySupported A X M) : map (LinearMap.id : M →ₗ[A] M) f = f :=
  (rfl)

/-- Pushing forward along `ψ ∘ φ` is pushing forward along `φ` and then along `ψ`. -/
theorem map_comp {P : Type*} [AddCommMonoid P] [Module C P] {τ : B →+* C} {ρ : A →+* C}
    [RingHomCompTriple σ τ ρ] (ψ : N →ₛₗ[τ] P) (φ : M →ₛₗ[σ] N) (f : compactlySupported A X M) :
    map (ψ.comp φ) f = map ψ (map φ f) :=
  (rfl)

end Map

end LocallyConstant.compactlySupported
