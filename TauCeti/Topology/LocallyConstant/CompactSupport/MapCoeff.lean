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
`C_c^∞(X, M) → C_c^∞(X, N)` (`LocallyConstant.compactlySupported.map`). Taking `φ = σ` gives the
change of coefficients `C_c^∞(X, A) → C_c^∞(X, B)` (`LocallyConstant.compactlySupported.mapCoeff`),
functorial in `σ` and sending the indicator `1_K • m` of a compact open set to `1_K • σ m`.

## Main definitions

* `LocallyConstant.compactlySupported.map φ`: the pushforward `C_c^∞(X, M) → C_c^∞(X, N)`,
  `f ↦ φ ∘ f`, along a semilinear map `φ`.
* `LocallyConstant.compactlySupported.mapCoeff φ`: the change of coefficients
  `C_c^∞(X, A) → C_c^∞(X, B)`, `f ↦ φ ∘ f`.

## Main results

* `LocallyConstant.compactlySupported.mapCoeff_compactOpenIndicator`: changing coefficients of
  `1_K • m` gives `1_K • φ m`.
* `LocallyConstant.compactlySupported.mapCoeff_id`,
  `LocallyConstant.compactlySupported.mapCoeff_comp`: functoriality of the change of coefficients.
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

end Map

/-- Change of coefficients of test functions: `f ↦ φ ∘ f`, a `φ`-semilinear map
`C_c^∞(X, A) → C_c^∞(X, B)`. -/
@[expose]
noncomputable def mapCoeff (φ : A →+* B) :
    compactlySupported A X A →ₛₗ[φ] compactlySupported B X B :=
  map φ.toSemilinearMap

/-- The value of `φ ∘ f` at `x` is `φ (f x)`. -/
@[simp]
theorem mapCoeff_apply (φ : A →+* B) (f : compactlySupported A X A) (x : X) :
    (mapCoeff φ f : LocallyConstant X B) x = φ ((f : LocallyConstant X A) x) :=
  (rfl)

/-- Changing coefficients of the indicator `1_K • m` gives the indicator `1_K • φ m`. -/
@[simp]
theorem mapCoeff_compactOpenIndicator [T2Space X] (φ : A →+* B) (K : CompactOpens X) (m : A) :
    mapCoeff φ ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ =
      ⟨compactOpenIndicator K (φ m), compactOpenIndicator_mem_compactlySupported K (φ m)⟩ :=
  Subtype.ext (map_compactOpenIndicator (map_zero φ) K m)

/-- Changing coefficients along the identity does nothing. -/
@[simp]
theorem mapCoeff_id (f : compactlySupported A X A) : mapCoeff (RingHom.id A) f = f :=
  (rfl)

/-- Changing coefficients along `ψ ∘ φ` is changing them along `φ` and then along `ψ`. -/
theorem mapCoeff_comp (ψ : B →+* C) (φ : A →+* B) (f : compactlySupported A X A) :
    mapCoeff (ψ.comp φ) f = mapCoeff ψ (mapCoeff φ f) :=
  (rfl)

end LocallyConstant.compactlySupported
