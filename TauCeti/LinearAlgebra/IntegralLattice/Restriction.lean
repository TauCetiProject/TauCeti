/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization
public import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Restricting an integral lattice to a submodule

A submodule `S` of an integral lattice `L` need not span the rational ambient space. Its
restricted integral form nevertheless defines a full integral lattice in `ℚ ⊗[ℤ] S`.
`IntegralLattice.restrict` constructs this lattice, and `restrictMap` embeds its ambient space
into that of `L`, preserving the forms. Its range is exactly the rational span of the embedded
submodule, and its integral carrier maps onto that submodule.
`isEven_restrict_iff` characterizes evenness by the original integral norm on the submodule.

When the embedded submodule is full, `restrictFull` instead keeps the original ambient space.
`restrictFullIsometry` identifies these two constructions through the canonical rational
extension of the inclusion. Neither construction assumes nondegeneracy: restrictions to
isotropic submodules and to the zero submodule are allowed.

These constructions let orthogonal summands be treated as lattices without imposing an
incorrect full-span hypothesis on each summand.

The rationalization uses `IntegralLattice.ofIntegralForm` and Mathlib's
`LinearMap.liftBaseChange`.

## Main declarations

* `TauCeti.IntegralLattice.restrict`: restriction in the submodule's own rational ambient space.
* `TauCeti.IntegralLattice.restrictCarrierEquiv`: the canonical integral carrier equivalence.
* `TauCeti.IntegralLattice.isEven_restrict_iff`: evenness characterized on the chosen submodule.
* `TauCeti.IntegralLattice.restrictMap`: the rational extension of the inclusion, characterized by
  `restrictMap_injective`, `range_restrictMap`, `form_restrictMap`, and
  `map_restrictMap_restrict_carrier`.
* `TauCeti.IntegralLattice.restrictFull`: restriction to a full ambient submodule contained in the
  original carrier, retaining the original rational ambient space.
* `TauCeti.IntegralLattice.restrictFullIsometry`: the canonical comparison of the two restrictions
  when the embedded submodule is full.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module TensorProduct

namespace TauCeti
namespace IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Restrict a lattice to an arbitrary submodule of its carrier, in that submodule's own rational
ambient space. Every such submodule is finite free over `ℤ`. -/
noncomputable def restrict (L : IntegralLattice V) (S : Submodule ℤ L) :
    IntegralLattice (ℚ ⊗[ℤ] S) :=
  ofIntegralForm (L.integralForm.restrict S) (L.isSymm_integralForm.restrict S)

/-- The form of a restricted lattice is the rational extension of the restricted integral form. -/
@[simp]
theorem restrict_form (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).form = (L.integralForm.restrict S).baseChange ℚ :=
  ofIntegralForm_form _ _

/-- The carrier of a restricted lattice is the range of the unit pure tensor map. -/
-- Leave membership normalization to the simp lemma `mem_restrict_carrier_iff`.
theorem restrict_carrier (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).carrier = LinearMap.range (TensorProduct.mk ℤ ℚ S 1) :=
  ofIntegralForm_carrier _ _

/-- The carrier of a restricted lattice consists of the unit pure tensors of the submodule. -/
@[simp]
theorem mem_restrict_carrier_iff (L : IntegralLattice V) (S : Submodule ℤ L)
    (x : ℚ ⊗[ℤ] S) : x ∈ (L.restrict S).carrier ↔ ∃ s : S, 1 ⊗ₜ[ℤ] s = x :=
  mem_ofIntegralForm_carrier_iff _ _ x

/-- The original submodule is canonically equivalent to the carrier of the restricted lattice. -/
noncomputable def restrictCarrierEquiv (L : IntegralLattice V) (S : Submodule ℤ L) :
    S ≃ₗ[ℤ] L.restrict S :=
  ofIntegralForm.carrierEquiv _ _

/-- The carrier equivalence sends a submodule vector to its unit pure tensor. -/
@[simp]
theorem coe_restrictCarrierEquiv_apply (L : IntegralLattice V) (S : Submodule ℤ L) (s : S) :
    (L.restrictCarrierEquiv S s : ℚ ⊗[ℤ] S) = 1 ⊗ₜ[ℤ] s :=
  ofIntegralForm.coe_carrierEquiv_apply _ _ s

/-- Restriction recovers the original integral form on the chosen submodule. -/
@[simp]
theorem integralForm_restrictCarrierEquiv (L : IntegralLattice V) (S : Submodule ℤ L) (s t : S) :
    (L.restrict S).integralForm (L.restrictCarrierEquiv S s) (L.restrictCarrierEquiv S t) =
      L.integralForm s t :=
  ofIntegralForm.integralForm_carrierEquiv _ _ s t

/-- Restriction recovers the original integral norm on the chosen submodule. -/
@[simp]
theorem integralNorm_restrictCarrierEquiv (L : IntegralLattice V) (S : Submodule ℤ L) (s : S) :
    (L.restrict S).integralNorm (L.restrictCarrierEquiv S s) = L.integralNorm s := by
  rw [integralNorm_apply, integralForm_restrictCarrierEquiv, integralNorm_apply]

/-- A restricted lattice is even exactly when the original integral norm is even on the
submodule. In particular restriction preserves evenness. -/
theorem isEven_restrict_iff (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).IsEven ↔ ∀ s : S, Even (L.integralNorm s) := by
  simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
    integralNorm_apply] using
    (L.restrict S).isEven_iff_of_integralForm_equiv (L.integralForm.restrict S)
      (L.restrictCarrierEquiv S) (fun s ↦ L.integralForm_restrictCarrierEquiv S s s)

/-- The rational extension of the inclusion of a submodule into the ambient space of a lattice. -/
def restrictMap (L : IntegralLattice V) (S : Submodule ℤ L) : ℚ ⊗[ℤ] S →ₗ[ℚ] V :=
  (L.carrier.subtype.comp S.subtype).liftBaseChange ℚ

/-- The rational inclusion sends a pure tensor to the scalar multiple of the embedded vector. -/
@[simp]
theorem restrictMap_tmul (L : IntegralLattice V) (S : Submodule ℤ L) (q : ℚ) (s : S) :
    L.restrictMap S (q ⊗ₜ[ℤ] s) = q • ((s : L) : V) :=
  LinearMap.liftBaseChange_tmul ℚ _ q s

/-- Rational extension of the inclusion remains injective. No nondegeneracy hypothesis on the
form is needed. -/
theorem restrictMap_injective (L : IntegralLattice V) (S : Submodule ℤ L) :
    Function.Injective (L.restrictMap S) :=
  (L.carrier.subtype.comp S.subtype).liftBaseChange_injective (K := ℚ)
    (L.carrier.injective_subtype.comp S.injective_subtype)

/-- The range of the rational inclusion is exactly the rational span of the embedded submodule. -/
theorem range_restrictMap (L : IntegralLattice V) (S : Submodule ℤ L) :
    LinearMap.range (L.restrictMap S) = Submodule.span ℚ (S.map L.carrier.subtype : Set V) := by
  rw [restrictMap, LinearMap.range_liftBaseChange, LinearMap.range_comp,
    Submodule.range_subtype]

/-- The rational inclusion preserves the forms, even if the restricted form is degenerate. -/
@[simp]
theorem form_restrictMap (L : IntegralLattice V) (S : Submodule ℤ L) (x y : ℚ ⊗[ℤ] S) :
    L.form (L.restrictMap S x) (L.restrictMap S y) = (L.restrict S).form x y := by
  rw [restrict_form]
  exact (L.integralForm.restrict S).liftBaseChange L.form
    (fun s t ↦ (L.integralForm_cast s t).symm) x y

/-- The restricted integral carrier maps onto the embedded submodule, not merely onto its
rational span. -/
theorem map_restrictMap_restrict_carrier (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).carrier.map ((L.restrictMap S).restrictScalars ℤ) = S.map L.carrier.subtype := by
  have hcomp : (L.restrictMap S).restrictScalars ℤ ∘ₗ TensorProduct.mk ℤ ℚ S 1 =
      L.carrier.subtype ∘ₗ S.subtype := by
    ext s
    -- `ext` leaves the composite behind linear-map coercions. Expose the applications of
    -- `restrictScalars` and `TensorProduct.mk` definitionally to use `restrictMap_tmul`.
    change L.restrictMap S (1 ⊗ₜ[ℤ] s) = ((s : L) : V)
    simp only [restrictMap_tmul, one_smul]
  rw [restrict_carrier]
  calc
    _ = LinearMap.range ((L.restrictMap S).restrictScalars ℤ ∘ₗ
        TensorProduct.mk ℤ ℚ S 1) := (LinearMap.range_comp _ _).symm
    _ = LinearMap.range (L.carrier.subtype ∘ₗ S.subtype) := congrArg LinearMap.range hcomp
    _ = S.map L.carrier.subtype := by
      rw [LinearMap.range_comp, Submodule.range_subtype]

/-- Restriction to a full ambient submodule contained in the carrier, retaining the original
rational ambient space. Fullness is supplied as an `IsLattice ℚ` instance. The constructor
`restrict` needs no span condition because it builds its own rational ambient space. -/
def restrictFull (L : IntegralLattice V) (N : Submodule ℤ V) (hN : N ≤ L.carrier)
    [N.IsLattice ℚ] : IntegralLattice V :=
  ofSubmodule N L.form L.isSymm (L.le_dualSubmodule_of_le_carrier hN)

/-- The carrier of the full restriction is the chosen ambient submodule. -/
@[simp]
theorem restrictFull_carrier (L : IntegralLattice V) (N : Submodule ℤ V) (hN : N ≤ L.carrier)
    [N.IsLattice ℚ] : (L.restrictFull N hN).carrier = N :=
  ofSubmodule_carrier _ _ _ _

/-- Full restriction retains the original rational form. -/
@[simp]
theorem restrictFull_form (L : IntegralLattice V) (N : Submodule ℤ V) (hN : N ≤ L.carrier)
    [N.IsLattice ℚ] : (L.restrictFull N hN).form = L.form :=
  ofSubmodule_form _ _ _ _

/-- Fullness supplies the surjectivity needed to bundle the comparison as an isometry. -/
private theorem restrictMap_bijective (L : IntegralLattice V) (S : Submodule ℤ L)
    [(S.map L.carrier.subtype).IsLattice ℚ] : Function.Bijective (L.restrictMap S) := by
  refine ⟨L.restrictMap_injective S, LinearMap.range_eq_top.mp ?_⟩
  rw [L.range_restrictMap S]
  exact Submodule.IsLattice.span_eq_top

/-- For a full submodule, restriction in its own rationalization is canonically isometric to
restriction in the original ambient space. The underlying map is the rational extension of the
inclusion, so this identifies both the carriers and the forms. -/
noncomputable def restrictFullIsometry (L : IntegralLattice V) (S : Submodule ℤ L)
    [(S.map L.carrier.subtype).IsLattice ℚ] : Isometry (L.restrict S)
      (L.restrictFull (S.map L.carrier.subtype) (L.carrier.map_subtype_le S)) :=
  Isometry.ofCarrierEquiv
    ((L.restrictCarrierEquiv S).symm.trans
      ((Submodule.equivMapOfInjective L.carrier.subtype L.carrier.injective_subtype S).trans
        (LinearEquiv.ofEq _ _ (L.restrictFull_carrier _
          (L.carrier.map_subtype_le S)).symm))) (by
    intro x y
    obtain ⟨s, rfl⟩ := (L.restrictCarrierEquiv S).surjective x
    obtain ⟨t, rfl⟩ := (L.restrictCarrierEquiv S).surjective y
    rw [integralForm_restrictCarrierEquiv]
    apply Int.cast_injective (α := ℚ)
    simp only [integralForm_cast, restrictFull_form, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.coe_ofEq_apply,
      Submodule.coe_equivMapOfInjective_apply,
      Submodule.subtype_apply])

/-- The canonical comparison applies the rational extension of the inclusion. -/
@[simp]
theorem restrictFullIsometry_apply (L : IntegralLattice V) (S : Submodule ℤ L)
    [(S.map L.carrier.subtype).IsLattice ℚ] (x : ℚ ⊗[ℤ] S) :
    L.restrictFullIsometry S x = L.restrictMap S x := by
  let e := (L.restrictCarrierEquiv S).symm.trans
    ((Submodule.equivMapOfInjective L.carrier.subtype L.carrier.injective_subtype S).trans
      (LinearEquiv.ofEq _ _ (L.restrictFull_carrier _ (L.carrier.map_subtype_le S)).symm))
  have he := LinearEquiv.eq_extendOfIsLattice e
    (LinearEquiv.ofBijective (L.restrictMap S) (L.restrictMap_bijective S)) (by
      intro y
      obtain ⟨s, rfl⟩ := (L.restrictCarrierEquiv S).surjective y
      simp only [e, LinearEquiv.ofBijective_apply, coe_restrictCarrierEquiv_apply,
        restrictMap_tmul, one_smul, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        LinearEquiv.coe_ofEq_apply, Submodule.coe_equivMapOfInjective_apply,
        Submodule.subtype_apply])
  -- Unfold only the comparison constructor to use its carrier-extension characterization.
  simp only [restrictFullIsometry, Isometry.ofCarrierEquiv_apply]
  exact (LinearEquiv.congr_fun he x).symm

end IntegralLattice
end TauCeti
