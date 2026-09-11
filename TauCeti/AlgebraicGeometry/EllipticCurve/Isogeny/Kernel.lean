/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.FixedField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree

/-!
# The kernel of an isogeny

An isogeny is a map of function fields, so it has no point map to take a fibre of. Its kernel is
read off the translation action instead: a point `P` of `W₁` lies in the kernel exactly when
translating by `P` moves no function pulled back from `W₂`. On the points where the two notions
can be compared this is the usual kernel, since `φ(X + P) = φ(X) + φ(P)`, and it is stated here
for every isogeny over every field, with no separability or rationality hypothesis.

The degree bounds the kernel: a pulled-back field of degree `d` is fixed by at most `d`
translations. The bound is often strict, because these are the `F`-rational points only: a
separable isogeny whose geometric kernel is not rational has fewer of them than its degree.
Equality needs separability *and* rationality of the whole geometric kernel, which is what the
point count `deg (1 − π_q) = #E(𝔽_q)` supplies for `1 − π` over a finite field; neither that
identity nor the general equality is proved here.

## Main definitions

* `TauCeti.Isogeny.ker`: the subgroup of points whose translation fixes the pulled-back field.

## Main results

* `TauCeti.Isogeny.card_ker_le_degree`: the kernel has at most `deg φ` elements.
* `TauCeti.Isogeny.ker_le_ker_comp`: postcomposition can only enlarge the kernel.
* `TauCeti.Isogeny.ker_eq_bot_of_degree_eq_one`: degree one forces a trivial kernel.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]

/-- **The kernel of an isogeny**: the points whose translation fixes every pulled-back function. -/
noncomputable def ker (φ : Isogeny W₁ W₂) : AddSubgroup (W₁⁄F).toAffine.Point :=
  translationFixingSubgroup W₁ φ.fieldPullback.fieldRange

/-- The defining equation of `ker`. -/
theorem ker_def (φ : Isogeny W₁ W₂) :
    φ.ker = translationFixingSubgroup W₁ φ.fieldPullback.fieldRange := (rfl)

/-- **A point is in the kernel exactly when it translates every pulled-back function to
itself.** -/
@[simp]
theorem mem_ker_iff {φ : Isogeny W₁ W₂} {P : (W₁⁄F).toAffine.Point} :
    P ∈ φ.ker ↔ ∀ z ∈ φ.fieldPullback.fieldRange, translation W₁ P z = z :=
  mem_translationFixingSubgroup_iff W₁

/-- **The kernel is finite**, the pulled-back field being of finite index. -/
instance finite_ker (φ : Isogeny W₁ W₂) : Finite φ.ker :=
  finite_translationFixingSubgroup W₁ φ.fieldPullback.fieldRange

/-- **The degree bounds the kernel**: an isogeny of degree `d` is fixed by at most `d`
translations. The bound is often strict, this being the rational kernel: equality needs the
isogeny to be separable and its geometric kernel to be rational. -/
theorem card_ker_le_degree (φ : Isogeny W₁ W₂) : Nat.card φ.ker ≤ φ.degree :=
  (card_translationFixingSubgroup_le W₁ φ.fieldPullback.fieldRange).trans_eq (φ.degree_def).symm

/-- **Postcomposition can only enlarge the kernel**: a function pulled back from `W₃` arrives
through `W₂`, so a translation fixing everything from `W₂` fixes it too. -/
theorem ker_le_ker_comp {W₃ : WeierstrassCurve.Affine F} (ψ : Isogeny W₂ W₃)
    (φ : Isogeny W₁ W₂) : φ.ker ≤ (ψ.comp φ).ker := by
  rw [ker_def, ker_def]
  refine translationFixingSubgroup_antitone W₁ ?_
  rintro _ ⟨z, rfl⟩
  exact AlgHom.mem_fieldRange.2 ⟨ψ.fieldPullback z, by rw [comp_fieldPullback]; rfl⟩

/-- **An isogeny of degree one has trivial kernel**, the bound leaving no room. -/
theorem ker_eq_bot_of_degree_eq_one {φ : Isogeny W₁ W₂} (h : φ.degree = 1) : φ.ker = ⊥ :=
  φ.ker.eq_bot_of_card_le (h ▸ φ.card_ker_le_degree)

/-- **The identity isogeny has trivial kernel.** -/
@[simp]
theorem ker_id (W : WeierstrassCurve.Affine F) [W.IsElliptic] : (id W).ker = ⊥ :=
  ker_eq_bot_of_degree_eq_one (degree_id W)

end TauCeti.Isogeny

end
