/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Verschiebung.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Naturality

/-!
# Naturality of Verschiebung

Verschiebung commutes with arbitrary field extension and is natural in isogenies of elliptic
curves. Over an imperfect field its source is the Frobenius twist, so the naturality square
uses the Frobenius twist of the isogeny. Under field extension the two possible source curves
are identified using the commutation of field homomorphisms with Frobenius.

These comparisons allow the factorization of multiplication by the characteristic into
relative Frobenius and Verschiebung to be transported between fields. They use the existing
identification of Verschiebung with the dual of relative Frobenius and the naturality of
relative Frobenius. No perfectness or algebraicity assumption on the field extension is needed.

## Main results

* `TauCeti.Isogeny.verschiebungIsogeny_map`: compatibility with field extension.
* `TauCeti.Isogeny.comp_verschiebungIsogeny`: the naturality square for an isogeny.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.
-/

public section

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p]

/-- Verschiebung commutes with arbitrary field extension, under the canonical identification
of the base change of the Frobenius twist with the Frobenius twist of the base change. -/
@[simp]
theorem verschiebungIsogeny_map {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] (f : F →+* K) :
    let := expChar_of_injective_ringHom f.injective p
    let e : (W.map (frobenius F p)).map f = (W.map f).map (frobenius K p) :=
      congrArg W.map (f.frobenius_comm p)
    (e ▸ (verschiebungIsogeny p W).map f) = verschiebungIsogeny p (W.map f) := by
  let := expChar_of_injective_ringHom f.injective p
  dsimp only
  -- Dualization reverses the arrow, so transport of the target becomes transport of the source.
  have transport {U V : WeierstrassCurve.Affine K} [U.IsElliptic] [V.IsElliptic]
      (e : U = V) (φ : Isogeny (W.map f) U) : (e ▸ φ.dual) = (e ▸ φ).dual := by
    subst V
    rfl
  rw [← dual_relativeFrobeniusIsogeny, dual_map]
  refine (transport _ _).trans ?_
  rw [relativeFrobeniusIsogeny_map, dual_relativeFrobeniusIsogeny]

/-- The Verschiebung square commutes with every isogeny: `φ ∘ V₁ = V₂ ∘ φ⁽ᵖ⁾`.
The isogeny on the right is Frobenius-twisted, including over imperfect fields.

This is not a simp lemma: when `φ` is relative Frobenius, the left side also rewrites by
`relativeFrobeniusIsogeny_comp`, producing a different naturality square. -/
theorem comp_verschiebungIsogeny {W₁ W₂ : WeierstrassCurve.Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] (φ : Isogeny W₁ W₂) :
    φ.comp (verschiebungIsogeny p W₁) =
      (verschiebungIsogeny p W₂).comp (φ.map (frobenius F p)) := by
  -- Precomposing by relative Frobenius reduces both sides to `φ ∘ [p] = [p] ∘ φ`.
  apply comp_right_injective (relativeFrobeniusIsogeny p W₁)
  simp only [comp_assoc, verschiebungIsogeny_comp_relativeFrobeniusIsogeny,
    ← relativeFrobeniusIsogeny_comp, comp_mulByIntIsogenyOfNeZero]
  rw [← comp_assoc, verschiebungIsogeny_comp_relativeFrobeniusIsogeny]

end TauCeti.Isogeny

end
