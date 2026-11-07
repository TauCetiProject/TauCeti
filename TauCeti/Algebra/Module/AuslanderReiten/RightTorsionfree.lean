/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
public import TauCeti.Algebra.Module.AuslanderReiten.Torsionfree
public import TauCeti.Algebra.Homology.Ext.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# `k`-torsionfree right modules are `k`-th syzygies

A right `A`-module is a left `Aᵐᵒᵖ`-module, so the left-module theory applied over `Aᵐᵒᵖ` describes
right modules. Its transposes are then modules over the double opposite `Aᵐᵒᵖᵐᵒᵖ`, with `Ext`
computed into `Aᵐᵒᵖ`. The natural transpose of a right module `N` is instead the left `A`-module
`Q.rightTranspose`, dualizing a finite projective presentation `Q` into `A`
(`TauCeti.FiniteProjectivePresentation.rightTranspose`). This file compares the two on `Ext`:
restriction of scalars along `A ≃+* Aᵐᵒᵖᵐᵒᵖ` is an equivalence of module categories carrying the
first transpose to the right transpose and `Aᵐᵒᵖ` to `A`, so the two `Ext` groups vanish together.

With this comparison, Auslander–Bridger's theorem that `k`-torsionfree modules are `k`-th syzygies
(`TauCeti.AuslanderReitenTranspose.isSyzygy_of_ext_eq_zero`) applies to right modules: if
`Ext^i(Tr N, A) = 0` for `1 ≤ i ≤ k`, where `Tr N` is the right transpose, then `N` is a `k`-th
syzygy of right modules.

## Main definitions

* `TauCeti.FiniteProjectivePresentation.restrictScalarsTransposeIso`: restricting scalars carries
  the transpose over `Aᵐᵒᵖ` to the right transpose.
* `TauCeti.FiniteProjectivePresentation.restrictScalarsOpIso`: restricting scalars carries the
  `Aᵐᵒᵖᵐᵒᵖ`-module `Aᵐᵒᵖ` to `A`.

## Main results

* `TauCeti.FiniteProjectivePresentation.ext_transpose_eq_zero_iff_ext_rightTranspose_eq_zero`:
  the two transposes have the same vanishing of `Ext` into the ring.
* `TauCeti.FiniteProjectivePresentation.isSyzygy_of_ext_rightTranspose_eq_zero`: `k`-torsionfree
  right modules are `k`-th syzygies.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Theorem 2.17.
-/

public section

open CategoryTheory CategoryTheory.Abelian

universe w u

namespace TauCeti.FiniteProjectivePresentation

variable {A : Type u} [Ring A] {N : ModuleCat.{u} Aᵐᵒᵖ} (Q : FiniteProjectivePresentation N)

/-- Restricting scalars along `A ≃+* Aᵐᵒᵖᵐᵒᵖ` carries the transpose of `Q` over `Aᵐᵒᵖ` to the right
transpose of `Q`. -/
noncomputable def restrictScalarsTransposeIso :
    (ModuleCat.restrictScalars.{u} (RingEquiv.opOp A).toRingHom).obj
      (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p)) ≅ Q.rightTranspose :=
  let X := (ModuleCat.restrictScalars.{u} (RingEquiv.opOp A).toRingHom).obj
    (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p))
  let e : X ≃ₗ[A] Q.rightTranspose :=
    { Q.rightTransposeEquiv.symm.toAddEquiv with
      map_smul' := fun a (x : AuslanderReitenTranspose Q.p) ↦
        (Q.rightTransposeEquiv.symm.map_smulₛₗ (RingEquiv.opOp A a) x).trans (by simp) }
  e.toModuleIso

variable (A) in
/-- Restricting scalars along `A ≃+* Aᵐᵒᵖᵐᵒᵖ` carries `Aᵐᵒᵖ`, the regular right module of `Aᵐᵒᵖ`, to
the regular module `A`. -/
noncomputable def restrictScalarsOpIso :
    (ModuleCat.restrictScalars.{u} (RingEquiv.opOp A).toRingHom).obj
      (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ) ≅ ModuleCat.of A A :=
  let X := (ModuleCat.restrictScalars.{u} (RingEquiv.opOp A).toRingHom).obj
    (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ)
  let e : X ≃ₗ[A] A :=
    { (MulOpposite.opAddEquiv : A ≃+ Aᵐᵒᵖ).symm with
      map_smul' := fun a (x : Aᵐᵒᵖ) ↦ by
        change MulOpposite.unop (x * MulOpposite.op a) = a * MulOpposite.unop x
        simp }
  e.toModuleIso

variable [HasExt.{w} (ModuleCat.{u} Aᵐᵒᵖᵐᵒᵖ)] [HasExt.{w} (ModuleCat.{u} A)]

/-- **Comparing the two transposes of a right module on `Ext`**: `Ext^n` of the transpose of `Q`
over `Aᵐᵒᵖ` into `Aᵐᵒᵖ`, computed over the double opposite, vanishes exactly when `Ext^n` of the
right transpose of `Q` into `A` vanishes. Restriction of scalars along `A ≃+* Aᵐᵒᵖᵐᵒᵖ` is an
equivalence of module categories, which preserves `Ext`. -/
theorem ext_transpose_eq_zero_iff_ext_rightTranspose_eq_zero (n : ℕ) :
    (∀ e : Ext.{w} (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p))
      (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ) n, e = 0) ↔
      ∀ e : Ext.{w} Q.rightTranspose (ModuleCat.of A A) n, e = 0 := by
  let E := (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)).extAddEquiv.{w, w}
    (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ (AuslanderReitenTranspose Q.p)) (ModuleCat.of Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ) n |>.trans
    (extAddEquivOfIso Q.restrictScalarsTransposeIso (restrictScalarsOpIso A) n)
  exact ⟨fun h e ↦ by simpa using congrArg E (h (E.symm e)),
    fun h e ↦ E.injective (by rw [h (E e), map_zero])⟩

end TauCeti.FiniteProjectivePresentation

namespace TauCeti

variable {A : Type u} [Ring A] [HasExt.{w} (ModuleCat.{u} Aᵐᵒᵖᵐᵒᵖ)] [HasExt.{w} (ModuleCat.{u} A)]

/-- **`k`-torsionfree right modules are `k`-th syzygies** (Auslander-Bridger): over a left
Noetherian ring `A`, if a right module `N` has a finite projective presentation `Q` whose right
transpose `Tr N` satisfies `Ext^i(Tr N, A) = 0` for `1 ≤ i ≤ k`, then there is an exact sequence
`0 ⟶ N ⟶ Q₁ ⟶ ⋯ ⟶ Q_k` of right modules with every `Qᵢ` finitely generated projective. This is
`TauCeti.AuslanderReitenTranspose.isSyzygy_of_ext_eq_zero` over `Aᵐᵒᵖ`, read through
`TauCeti.FiniteProjectivePresentation.ext_transpose_eq_zero_iff_ext_rightTranspose_eq_zero`. -/
theorem FiniteProjectivePresentation.isSyzygy_of_ext_rightTranspose_eq_zero [IsNoetherianRing A]
    {N : ModuleCat.{u} Aᵐᵒᵖ} (Q : FiniteProjectivePresentation N) (k : ℕ)
    (hext : ∀ i, 0 < i → i ≤ k → ∀ e : Ext.{w} Q.rightTranspose (ModuleCat.of A A) i, e = 0) :
    ObjectProperty.IsSyzygy
      (fun X : ModuleCat.{u} Aᵐᵒᵖ ↦ Module.Finite Aᵐᵒᵖ X ∧ Module.Projective Aᵐᵒᵖ X) k N := by
  have : IsNoetherianRing Aᵐᵒᵖᵐᵒᵖ := isNoetherianRing_of_ringEquiv A (RingEquiv.opOp A)
  have := Q.finite₀
  have := Q.finite₁
  have := Q.projective₀
  have := Q.projective₁
  exact AuslanderReitenTranspose.isSyzygy_of_ext_eq_zero Q.exact Q.surjective k
    fun i hi hik ↦ (Q.ext_transpose_eq_zero_iff_ext_rightTranspose_eq_zero i).2 (hext i hi hik)

end TauCeti
