/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.LocallyConstant.CompactSupport

/-!
# Change of coefficients for locally constant functions with compact support

Let `X` be a topological space and `φ : A →+* B` a homomorphism of semirings. Composing with `φ`
sends a locally constant function `f : X → A` with compact support to `φ ∘ f`, which again has
compact support since `φ 0 = 0`. This is a `φ`-semilinear map
`C_c^∞(X, A) → C_c^∞(X, B)` (`LocallyConstant.compactlySupported.mapCoeff`), functorial in `φ`,
sending the indicator `1_K • m` of a compact open set to `1_K • φ m`.

## Main definitions

* `LocallyConstant.compactlySupported.mapCoeff φ`: the change of coefficients
  `C_c^∞(X, A) → C_c^∞(X, B)`, `f ↦ φ ∘ f`.

## Main results

* `LocallyConstant.map_compactOpenIndicator`: composing the indicator `1_K • m` with a map
  preserving `0` gives the indicator `1_K • f m`.
* `LocallyConstant.compactlySupported.mapCoeff_compactOpenIndicator`: changing coefficients of
  `1_K • m` gives `1_K • φ m`.
* `LocallyConstant.compactlySupported.mapCoeff_id`,
  `LocallyConstant.compactlySupported.mapCoeff_comp`: functoriality of the change of coefficients.
-/

public section

open TopologicalSpace

namespace LocallyConstant

variable {X M N : Type*} [TopologicalSpace X]

/-- Composing the indicator `1_K • m` of a compact open set with a map `f` preserving `0` gives the
indicator `1_K • f m`. -/
@[simp]
theorem map_compactOpenIndicator [T2Space X] [Zero M] [Zero N] {f : M → N} (hf : f 0 = 0)
    (K : CompactOpens X) (m : M) :
    (compactOpenIndicator K m).map f = compactOpenIndicator K (f m) :=
  ext fun x => by by_cases hx : x ∈ K <;> simp [hx, hf]

namespace compactlySupported

variable {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]

/-- Change of coefficients of test functions: `f ↦ φ ∘ f`, a `φ`-semilinear map
`C_c^∞(X, A) → C_c^∞(X, B)`. -/
noncomputable def mapCoeff (φ : A →+* B) :
    compactlySupported A X A →ₛₗ[φ] compactlySupported B X B where
  toFun f := ⟨(f : LocallyConstant X A).map φ,
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).comp_left (map_zero φ))⟩
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp

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

end compactlySupported

end LocallyConstant
