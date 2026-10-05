/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization

/-!
# Restricting an integral lattice to a submodule

A submodule `S` of an integral lattice `L` need not span the rational ambient space. Its
restricted integral form nevertheless defines a full integral lattice in `ℚ ⊗[ℤ] S`.
`IntegralLattice.restrict` constructs this lattice, and `restrictMap` embeds its ambient space
into that of `L`, preserving the forms. Its range is exactly the rational span of the embedded
submodule, and its integral carrier maps onto that submodule.

When the embedded submodule is full, `restrictFull` instead keeps the original ambient space.
`restrictFullIsometry` identifies these two constructions through the canonical rational
extension of the inclusion. Neither construction assumes nondegeneracy: restrictions to
isotropic submodules and to the zero submodule are allowed.

These constructions let orthogonal summands be treated as lattices without imposing an
incorrect full-span hypothesis on each summand.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* The rationalization uses `IntegralLattice.ofIntegralForm` and Mathlib's
  `LinearMap.liftBaseChange`.
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

/-- The carrier of a restricted lattice consists of the unit pure tensors of the submodule. -/
@[simp]
theorem mem_restrict_carrier_iff (L : IntegralLattice V) (S : Submodule ℤ L)
    (x : ℚ ⊗[ℤ] S) : x ∈ (L.restrict S).carrier ↔ ∃ s : S, 1 ⊗ₜ[ℤ] s = x :=
  mem_ofIntegralForm_carrier_iff _ _ x

/-- The original submodule is canonically equivalent to the carrier of the restricted lattice. -/
noncomputable def restrictCarrierEquiv (L : IntegralLattice V) (S : Submodule ℤ L) :
    S ≃ₗ[ℤ] L.restrict S :=
  ofIntegralForm.carrierEquiv _ _

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

/-- A restricted lattice is even exactly when the original integral norm is even on the
submodule. In particular restriction preserves evenness. -/
theorem isEven_restrict_iff (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).IsEven ↔ ∀ s : S, Even (L.integralNorm s) := by
  have hnorm (s : S) : (L.restrict S).norm (L.restrictCarrierEquiv S s) = L.norm (s : L) := by
    rw [← integralNorm_cast, ← L.integralNorm_cast, integralNorm_apply,
      integralForm_restrictCarrierEquiv, integralNorm_apply]
  rw [isEven_iff_forall_norm]
  constructor
  · intro h s
    exact (L.even_integralNorm_iff s).mpr (by
      simpa only [hnorm] using h (L.restrictCarrierEquiv S s))
  · intro h x
    obtain ⟨s, rfl⟩ := (L.restrictCarrierEquiv S).surjective x
    simpa only [hnorm] using (L.even_integralNorm_iff s).mp (h s)

/-- The rational extension of the inclusion of a submodule into the ambient space of a lattice. -/
def restrictMap (L : IntegralLattice V) (S : Submodule ℤ L) : ℚ ⊗[ℤ] S →ₗ[ℚ] V :=
  (L.carrier.subtype.comp S.subtype).liftBaseChange ℚ

@[simp]
theorem restrictMap_tmul (L : IntegralLattice V) (S : Submodule ℤ L) (q : ℚ) (s : S) :
    L.restrictMap S (q ⊗ₜ[ℤ] s) = q • ((s : L) : V) :=
  LinearMap.liftBaseChange_tmul ℚ _ q s

/-- Rational extension of the inclusion remains injective. No nondegeneracy hypothesis on the
form is needed. -/
theorem restrictMap_injective (L : IntegralLattice V) (S : Submodule ℤ L) :
    Function.Injective (L.restrictMap S) := by
  rw [restrictMap, LinearMap.liftBaseChange_injective_iff _ (Module.Free.chooseBasis ℤ S)]
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    ((Module.Free.chooseBasis ℤ S).linearIndependent.map'
      (L.carrier.subtype.comp S.subtype)
      (LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp Subtype.val_injective)))

/-- The range of the rational inclusion is exactly the rational span of the embedded submodule. -/
theorem range_restrictMap (L : IntegralLattice V) (S : Submodule ℤ L) :
    LinearMap.range (L.restrictMap S) = Submodule.span ℚ (S.map L.carrier.subtype : Set V) := by
  rw [restrictMap, LinearMap.range_liftBaseChange, LinearMap.range_comp,
    Submodule.range_subtype]

/-- The rational inclusion preserves the forms, even if the restricted form is degenerate. -/
@[simp]
theorem form_restrictMap (L : IntegralLattice V) (S : Submodule ℤ L) (x y : ℚ ⊗[ℤ] S) :
    L.form (L.restrictMap S x) (L.restrictMap S y) = (L.restrict S).form x y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul q s =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul r t =>
      simp only [restrictMap_tmul, restrict_form, LinearMap.BilinForm.baseChange_tmul,
        LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, zsmul_eq_mul,
        L.integralForm_cast]
      ring

/-- The restricted integral carrier maps onto the embedded submodule, not merely onto its
rational span. -/
theorem map_restrict_carrier (L : IntegralLattice V) (S : Submodule ℤ L) :
    (L.restrict S).carrier.map ((L.restrictMap S).restrictScalars ℤ) = S.map L.carrier.subtype := by
  ext x
  simp only [Submodule.mem_map, mem_restrict_carrier_iff]
  constructor
  · rintro ⟨y, ⟨s, rfl⟩, rfl⟩
    exact ⟨(s : L), s.2, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨1 ⊗ₜ[ℤ] (⟨s, hs⟩ : S), ⟨⟨s, hs⟩, rfl⟩, by simp⟩

/-- Restriction to a full submodule, retaining the original rational ambient space. Fullness of
the embedded submodule is an explicit hypothesis, unlike in `restrict`. -/
def restrictFull (L : IntegralLattice V) (S : Submodule ℤ L)
    [(S.map L.carrier.subtype).IsLattice ℚ] : IntegralLattice V :=
  ofSubmodule (S.map L.carrier.subtype) L.form L.isSymm (by
    rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    exact L.form_mem_one s t)

@[simp]
theorem restrictFull_carrier (L : IntegralLattice V) (S : Submodule ℤ L)
    [(S.map L.carrier.subtype).IsLattice ℚ] :
    (L.restrictFull S).carrier = S.map L.carrier.subtype :=
  ofSubmodule_carrier _ _ _ _

@[simp]
theorem restrictFull_form (L : IntegralLattice V) (S : Submodule ℤ L)
    [(S.map L.carrier.subtype).IsLattice ℚ] : (L.restrictFull S).form = L.form :=
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
    [(S.map L.carrier.subtype).IsLattice ℚ] : Isometry (L.restrict S) (L.restrictFull S) where
  toIsometryEquiv :=
    { toLinearEquiv := LinearEquiv.ofBijective (L.restrictMap S) (L.restrictMap_bijective S)
      map_app' x y := by
        simp only [restrictFull_form, LinearEquiv.coe_coe, AddHom.toFun_eq_coe,
          LinearMap.coe_toAddHom, LinearEquiv.ofBijective_apply]
        exact L.form_restrictMap S x y }
  map_carrier := by
    rw [restrictFull_carrier]
    exact L.map_restrict_carrier S

@[simp]
theorem restrictFullIsometry_apply (L : IntegralLattice V) (S : Submodule ℤ L)
    [(S.map L.carrier.subtype).IsLattice ℚ] (x : ℚ ⊗[ℤ] S) :
    L.restrictFullIsometry S x = L.restrictMap S x := (rfl)

end IntegralLattice
end TauCeti
