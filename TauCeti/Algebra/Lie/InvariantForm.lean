/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import TauCeti.Algebra.Lie.Dual

/-!
# Invariant bilinear forms on irreducible Lie modules

A bilinear form `Φ` on a Lie module `M` is invariant when `Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆`
(`LinearMap.BilinForm.lieInvariant`). This file collects the invariant symmetric forms into the
submodule `TauCeti.LieModule.invariantForms R L M` and shows that on a finite-dimensional
irreducible module over an algebraically closed field there is at most one invariant form up to
scalars.

The reason is Schur's lemma. Invariance of `Φ` says exactly that `Φ`, read as a linear map
`M → M*`, is a morphism of Lie modules (`LinearMap.BilinForm.lieInvariant_iff` together with
`LieModule.maxTrivLinearMapEquivLieModuleHom`), and the morphism space between the irreducible
modules `M` and `M*` is at most a line (`TauCeti.LieModule.finrank_lieModuleHom_le_one`, with
`TauCeti.LieModule.isIrreducible_dual`). No nondegeneracy or symmetry of the forms is needed.

For the adjoint module of a simple Lie algebra this makes every invariant form a multiple of the
Killing form; that consequence is `TauCeti/Algebra/Lie/Killing/InvariantForm.lean`.

## Main definitions

* `TauCeti.LieModule.invariantForms`: the submodule of invariant symmetric bilinear forms on a Lie
  module.

## Main results

* `TauCeti.LieModule.traceForm_mem_invariantForms`: the trace form of a Lie module, in particular
  the Killing form, is an invariant symmetric form on the Lie algebra.
* `TauCeti.LieModule.invariantForms_le_maxTrivSubmodule`: invariant symmetric forms lie in the
  maximal trivial submodule of the space of bilinear forms.
* `TauCeti.LieModule.finrank_maxTrivSubmodule_bilinForm_le_one`: the invariant bilinear forms on a
  finite-dimensional irreducible module over an algebraically closed field form a space of
  dimension at most one.
* `TauCeti.LieModule.finrank_invariantForms_le_one`: so do the invariant symmetric forms.
* `TauCeti.LieModule.exists_eq_smul_of_lieInvariant`: on such a module, every invariant form is a
  scalar multiple of any nonzero invariant form.
* `TauCeti.LieModule.invariantForms_eq_span_singleton`: the invariant symmetric forms are the line
  spanned by any nonzero one.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §6.1 for
  Schur's lemma.
-/

public section

open Module (Dual finrank)

namespace TauCeti.LieModule

/-! ### The submodule of invariant symmetric forms -/

section CommRing

variable (R L M : Type*) [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- The invariant symmetric bilinear forms on a Lie module `M`: the forms `Φ` with
`Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆` and `Φ y z = Φ z y`. -/
def invariantForms : Submodule R (LinearMap.BilinForm R M) where
  carrier := {Φ | Φ.lieInvariant L ∧ Φ.IsSymm}
  zero_mem' := ⟨fun _ _ _ ↦ by simp, LinearMap.BilinForm.isSymm_zero⟩
  add_mem' {Φ Ψ} hΦ hΨ :=
    ⟨fun x y z ↦ by simp only [LinearMap.add_apply, hΦ.1 x y z, hΨ.1 x y z, neg_add],
      hΦ.2.add hΨ.2⟩
  smul_mem' c Φ hΦ := ⟨fun x y z ↦ by simp [hΦ.1 x y z], hΦ.2.smul c⟩

variable {R L M} in
@[simp]
theorem mem_invariantForms_iff {Φ : LinearMap.BilinForm R M} :
    Φ ∈ invariantForms R L M ↔ Φ.lieInvariant L ∧ Φ.IsSymm :=
  Iff.rfl

variable [LieAlgebra R L] [_root_.LieModule R L M]

/-- The trace form of a Lie module `M` is an invariant symmetric form on the Lie algebra `L`. For
`M = L` this is the Killing form `killingForm R L`. -/
theorem traceForm_mem_invariantForms :
    _root_.LieModule.traceForm R L M ∈ invariantForms R L L :=
  ⟨_root_.LieModule.traceForm_lieInvariant R L M,
    LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm R L M)⟩

/-- Invariant symmetric forms lie in the maximal trivial submodule of the space of bilinear forms,
which consists of the invariant forms by `LinearMap.BilinForm.lieInvariant_iff`. -/
theorem invariantForms_le_maxTrivSubmodule :
    invariantForms R L M ≤
      (_root_.LieModule.maxTrivSubmodule R L (LinearMap.BilinForm R M)).toSubmodule :=
  fun Φ hΦ ↦ Φ.lieInvariant_iff.mp hΦ.1

end CommRing

/-! ### Invariant forms on an irreducible module -/

section IsAlgClosed

variable {K L M : Type*} [Field K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M] [_root_.LieModule K L M]
variable [FiniteDimensional K M] [_root_.LieModule.IsIrreducible K L M]

variable (K L M) in
/-- **The invariant bilinear forms on a finite-dimensional irreducible Lie module over an
algebraically closed field form a space of dimension at most one.** Here the invariant forms are
described as the maximal trivial submodule of the space of bilinear forms, as in
`LinearMap.BilinForm.lieInvariant_iff`. -/
theorem finrank_maxTrivSubmodule_bilinForm_le_one :
    finrank K (_root_.LieModule.maxTrivSubmodule K L (LinearMap.BilinForm K M)) ≤ 1 := by
  have _i := isIrreducible_dual (K := K) (L := L) (M := M)
  rw [(_root_.LieModule.maxTrivLinearMapEquivLieModuleHom (R := K) (L := L) (M := M)
    (N := Dual K M)).finrank_eq]
  exact finrank_lieModuleHom_le_one K L

/-- **Invariant bilinear forms on a finite-dimensional irreducible Lie module over an algebraically
closed field are proportional**: every invariant form is a scalar multiple of any nonzero one. -/
theorem exists_eq_smul_of_lieInvariant {Φ Ψ : LinearMap.BilinForm K M} (hΦ : Φ.lieInvariant L)
    (hΨ : Ψ.lieInvariant L) (hΨ0 : Ψ ≠ 0) : ∃ c : K, Φ = c • Ψ := by
  let W := _root_.LieModule.maxTrivSubmodule K L (LinearMap.BilinForm K M)
  let Ψ' : W := ⟨Ψ, Ψ.lieInvariant_iff.mp hΨ⟩
  have hΨ' : Ψ' ≠ 0 := fun h ↦ hΨ0 (congrArg Subtype.val h)
  have _i : Nontrivial W := ⟨⟨Ψ', 0, hΨ'⟩⟩
  have hpos : 0 < finrank K W := Module.finrank_pos (R := K) (M := W)
  have hW : finrank K W = 1 := le_antisymm (finrank_maxTrivSubmodule_bilinForm_le_one K L M) hpos
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hW hΨ' ⟨Φ, Φ.lieInvariant_iff.mp hΦ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

variable (K L M) in
/-- The invariant symmetric bilinear forms on a finite-dimensional irreducible Lie module over an
algebraically closed field form a space of dimension at most one. -/
theorem finrank_invariantForms_le_one : finrank K (invariantForms K L M) ≤ 1 :=
  (Submodule.finrank_mono (R := K) (M := LinearMap.BilinForm K M)
    (invariantForms_le_maxTrivSubmodule K L M)).trans
    (finrank_maxTrivSubmodule_bilinForm_le_one K L M)

/-- On a finite-dimensional irreducible Lie module over an algebraically closed field, the
invariant symmetric bilinear forms are the line spanned by any nonzero one. -/
theorem invariantForms_eq_span_singleton {Ψ : LinearMap.BilinForm K M}
    (hΨ : Ψ ∈ invariantForms K L M) (hΨ0 : Ψ ≠ 0) : invariantForms K L M = K ∙ Ψ := by
  refine le_antisymm (fun Φ hΦ ↦ ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr hΨ)
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_lieInvariant hΦ.1 hΨ.1 hΨ0
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self Ψ)

end IsAlgClosed

end TauCeti.LieModule
