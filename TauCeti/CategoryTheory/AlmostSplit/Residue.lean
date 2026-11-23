/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import TauCeti.Algebra.Homology.ShortComplex.LocalEnd
public import TauCeti.CategoryTheory.AlmostSplit.Uniqueness
public import TauCeti.CategoryTheory.AlmostSplit.Valuation
public import TauCeti.RingTheory.Jacobson.MulOpposite
public import TauCeti.RingTheory.LocalRing.Residue

/-!
# The residue division rings of the end terms of an almost-split sequence

Let `0 → A → B → C → 0` be an almost-split sequence in a balanced preadditive category; its end
terms `A` and `C` have local endomorphism rings. Every endomorphism `e` of `C` is the third
component of an endomorphism `φ` of the sequence, and the class of its first component `φ.τ₁`
modulo the radical of `End A` depends only on `e`: an endomorphism of the sequence vanishing at
`C` is a non-isomorphism at `A`, since otherwise it would split the first map
(`CategoryTheory.ShortComplex.not_isIso_τ₁_of_τ₃_eq_zero`). This defines a ring
isomorphism between the residue division rings

`End C / rad(End C) ≃+* End A / rad(End A)`

(`CategoryTheory.ShortComplex.IsAlmostSplit.residueRingEquiv`), characterized by sending the class
of `φ.τ₃` to the class of `φ.τ₁` for every endomorphism `φ` of the sequence. It is an isomorphism
of algebras over the base ring of a linear category
(`CategoryTheory.ShortComplex.IsAlmostSplit.residueAlgEquiv`).

Over a field `k`, the two residue division rings therefore have the same dimension, and together
with the tower law of `TauCeti/CategoryTheory/Preadditive/Radical/Valuation.lean` and the
multiplicity count of `TauCeti/CategoryTheory/AlmostSplit/Valuation.lean` this gives the second
half of the valued mesh relation: for every object `X` with a local endomorphism ring, the first
entry of the valuation of `Irr(X, C)` is the second entry of the valuation of `Irr(A, X)`
(`CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_fst_eq_snd`). Together
with `CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_snd_eq_fst`, the
valuation of `A → X` is the valuation of `X → C` with its two entries exchanged.

## Main definitions

* `CategoryTheory.ShortComplex.IsAlmostSplit.residueRingEquiv`: the isomorphism
  `End C / rad(End C) ≃+* End A / rad(End A)`.
* `CategoryTheory.ShortComplex.IsAlmostSplit.residueAlgEquiv`: the same isomorphism, as an
  isomorphism of algebras over the base ring.

## Main results

* `CategoryTheory.ShortComplex.IsAlmostSplit.exists_hom_self_τ₃_eq`: every endomorphism of
  `C` extends to an endomorphism of the sequence, and
  `CategoryTheory.ShortComplex.IsAlmostSplit.exists_hom_self_τ₁_eq`: so does every endomorphism
  of `A`.
* `CategoryTheory.ShortComplex.IsAlmostSplit.isIso_τ₁_iff_isIso_τ₃`: an endomorphism of the
  sequence is invertible at `A` exactly when it is invertible at `C`.
* `CategoryTheory.ShortComplex.IsAlmostSplit.residueRingEquiv_mk`: the characterizing equation.
* `CategoryTheory.ShortComplex.IsAlmostSplit.finrank_residue_X₁_eq_finrank_residue_X₃`: over a
  field, the residue division rings of `A` and `C` have the same dimension.
* `CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_fst_eq_snd`: the first
  entry of the valuation of `Irr(X, C)` is the second entry of the valuation of `Irr(A, X)`, and
  `CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_X₁_eq_swap`: the
  valuation of `Irr(A, X)` is that of `Irr(X, C)` with its entries exchanged.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section VII.1, in particular Proposition VII.1.5.
-/

public section

open CategoryTheory CategoryTheory.Limits Module TauCeti

namespace CategoryTheory.ShortComplex.IsAlmostSplit

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] {S : ShortComplex C}

/-! ### Endomorphisms of an almost-split sequence -/

/-- The class modulo the radical of the first component of an endomorphism of an almost-split
sequence depends only on its third component. -/
private theorem mk_τ₁_eq_mk_τ₁ (hS : S.IsAlmostSplit) {φ ψ : S ⟶ S} (h : φ.τ₃ = ψ.τ₃) :
    Ideal.Quotient.mk (Ring.jacobson (End S.X₁)) (.of φ.τ₁) =
      Ideal.Quotient.mk (Ring.jacobson (End S.X₁)) (.of ψ.τ₁) := by
  have := hS.isLeftAlmostSplit_f.isLocalRing_end
  rw [Ideal.Quotient.eq, IsLocalRing.mem_jacobson_iff_not_isUnit]
  have h0 : (φ - ψ).τ₃ = 0 := by simp [h]
  simpa [isUnit_iff_isIso] using ShortComplex.not_isIso_τ₁_of_τ₃_eq_zero hS.shortExact.fIsKernel
    hS.isLeftAlmostSplit_f.not_isSplitMono (φ - ψ) h0

/-- **Every endomorphism of the left-hand end of an almost-split sequence extends to an
endomorphism of the sequence.** -/
theorem exists_hom_self_τ₁_eq (hS : S.IsAlmostSplit) (a : S.X₁ ⟶ S.X₁) :
    ∃ φ : S ⟶ S, φ.τ₁ = a := by
  have := hS.isLeftAlmostSplit_f.isLocalRing_end
  have hf : ¬ IsSplitMono (a ≫ S.f) := fun h ↦ by
    have : IsSplitMono a := isSplitMono_of_isSplitMono_comp a S.f
    have : IsIso a := by
      by_contra ha
      exact (mem_jacobsonRadical_iff_not_isSplitMono.mp
        (mem_jacobsonRadical_iff_not_isIso.mpr ha)) this
    exact (hS.isLeftAlmostSplit_f.iso_comp a).not_isSplitMono h
  obtain ⟨β, hβ⟩ := hS.isLeftAlmostSplit_f.factors S.X₂ (a ≫ S.f) hf
  obtain ⟨γ, hγ⟩ := CokernelCofork.IsColimit.desc' hS.shortExact.gIsCokernel (β ≫ S.g)
    (by rw [← Category.assoc, hβ, Category.assoc, S.zero, comp_zero])
  exact ⟨⟨a, β, γ, hβ.symm, hγ.symm⟩, rfl⟩

/-- **Every endomorphism of the right-hand end of an almost-split sequence extends to an
endomorphism of the sequence.** -/
theorem exists_hom_self_τ₃_eq (hS : S.IsAlmostSplit) (e : S.X₃ ⟶ S.X₃) :
    ∃ φ : S ⟶ S, φ.τ₃ = e := by
  have := hS.isRightAlmostSplit_g.isLocalRing_end
  refine hS.isRightAlmostSplit_g.exists_hom_τ₃_eq_of_not_isSplitEpi hS.shortExact.fIsKernel e
    fun h ↦ ?_
  have : IsSplitEpi e := isSplitEpi_of_isSplitEpi_comp S.g e
  have : IsIso e := by
    by_contra he
    exact (mem_jacobsonRadical_iff_not_isSplitEpi.mp (mem_jacobsonRadical_iff_not_isIso.mpr he))
      this
  exact (hS.isRightAlmostSplit_g.comp_iso e).not_isSplitEpi h

/-- **An endomorphism of an almost-split sequence is invertible at the left-hand end exactly when
it is invertible at the right-hand end.** -/
theorem isIso_τ₁_iff_isIso_τ₃ (hS : S.IsAlmostSplit) (φ : S ⟶ S) : IsIso φ.τ₁ ↔ IsIso φ.τ₃ := by
  have := hS.isRightAlmostSplit_g.isLocalRing_end
  refine ⟨fun hφ ↦ by_contra fun he ↦ ?_, fun _ ↦ hS.isIso_τ₁_of_isIso_τ₃ hS
    hS.shortExact.fIsKernel φ⟩
  -- A non-invertible `φ.τ₃` factors through `S.g`, so it is also the third component of an
  -- endomorphism with vanishing first component; the difference vanishes at the right-hand end.
  obtain ⟨t, ht⟩ := hS.isRightAlmostSplit_g.factors S.X₃ φ.τ₃
    (mem_jacobsonRadical_iff_not_isSplitEpi.mp (mem_jacobsonRadical_iff_not_isIso.mpr he))
  let χ : S ⟶ S :=
    { τ₁ := 0
      τ₂ := S.g ≫ t
      τ₃ := φ.τ₃
      comm₁₂ := by simp
      comm₂₃ := by rw [Category.assoc, ht] }
  refine ShortComplex.not_isIso_τ₁_of_τ₃_eq_zero hS.shortExact.fIsKernel
    hS.isLeftAlmostSplit_f.not_isSplitMono (φ - χ) (by simp [χ]) ?_
  simpa [χ] using hφ

/-! ### The residue isomorphism -/

/-- The ring homomorphism `End C → End A / rad(End A)` sending `e` to the class of the first
component of any endomorphism of the sequence extending `e`. -/
private noncomputable def residueEndHom (hS : S.IsAlmostSplit) :
    End S.X₃ →+* End S.X₁ ⧸ Ring.jacobson (End S.X₁) where
  toFun e := Ideal.Quotient.mk _ (.of (hS.exists_hom_self_τ₃_eq e.asHom).choose.τ₁)
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk _)]
    exact hS.mk_τ₁_eq_mk_τ₁ ((hS.exists_hom_self_τ₃_eq _).choose_spec.trans
      (ShortComplex.id_τ₃ S).symm)
  map_mul' e e' := by
    rw [← map_mul]
    exact hS.mk_τ₁_eq_mk_τ₁ (φ := (hS.exists_hom_self_τ₃_eq (e * e').asHom).choose)
      (ψ := (hS.exists_hom_self_τ₃_eq e'.asHom).choose ≫
        (hS.exists_hom_self_τ₃_eq e.asHom).choose)
      (by simp [(hS.exists_hom_self_τ₃_eq _).choose_spec])
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk _)]
    exact hS.mk_τ₁_eq_mk_τ₁ (ψ := 0) ((hS.exists_hom_self_τ₃_eq _).choose_spec)
  map_add' e e' := by
    rw [← map_add]
    exact hS.mk_τ₁_eq_mk_τ₁ (φ := (hS.exists_hom_self_τ₃_eq (e + e').asHom).choose)
      (ψ := (hS.exists_hom_self_τ₃_eq e.asHom).choose +
        (hS.exists_hom_self_τ₃_eq e'.asHom).choose)
      (by simp [(hS.exists_hom_self_τ₃_eq _).choose_spec])

private theorem residueEndHom_of_τ₃ (hS : S.IsAlmostSplit) (φ : S ⟶ S) :
    hS.residueEndHom (.of φ.τ₃) = Ideal.Quotient.mk _ (.of φ.τ₁) :=
  hS.mk_τ₁_eq_mk_τ₁ (hS.exists_hom_self_τ₃_eq _).choose_spec

/-- An endomorphism in the radical of `End C` is sent to zero. -/
private theorem residueEndHom_eq_zero_of_mem (hS : S.IsAlmostSplit) {e : End S.X₃}
    (he : e ∈ Ring.jacobson (End S.X₃)) : hS.residueEndHom e = 0 := by
  have := hS.isLeftAlmostSplit_f.isLocalRing_end
  have := hS.isRightAlmostSplit_g.isLocalRing_end
  obtain ⟨φ, hφ⟩ := hS.exists_hom_self_τ₃_eq e.asHom
  obtain rfl : End.of φ.τ₃ = e := End.ext hφ
  rw [IsLocalRing.mem_jacobson_iff_not_isUnit, isUnit_iff_isIso, ← hS.isIso_τ₁_iff_isIso_τ₃] at he
  rw [residueEndHom_of_τ₃, IsLocalRing.mk_jacobson_eq_zero_iff, isUnit_iff_isIso]
  exact he

/-- **The residue division rings of the two end terms of an almost-split sequence are
isomorphic**: `End C / rad(End C) ≃+* End A / rad(End A)`, sending the class of the third
component of an endomorphism of the sequence to the class of its first component
(`CategoryTheory.ShortComplex.IsAlmostSplit.residueRingEquiv_mk`). -/
noncomputable def residueRingEquiv (hS : S.IsAlmostSplit) :
    End S.X₃ ⧸ Ring.jacobson (End S.X₃) ≃+* End S.X₁ ⧸ Ring.jacobson (End S.X₁) :=
  have := hS.isLeftAlmostSplit_f.isLocalRing_end
  have := hS.isRightAlmostSplit_g.isLocalRing_end
  .ofBijective (Ideal.Quotient.lift _ hS.residueEndHom fun _ ↦ hS.residueEndHom_eq_zero_of_mem)
    ⟨RingHom.injective _, fun x ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨φ, hφ⟩ := hS.exists_hom_self_τ₁_eq a.asHom
      refine ⟨Ideal.Quotient.mk _ (.of φ.τ₃), ?_⟩
      rw [Ideal.Quotient.lift_mk, residueEndHom_of_τ₃]
      exact congrArg _ (End.ext hφ)⟩

/-- **The characterizing equation of the residue isomorphism**: for every endomorphism `φ` of the
almost-split sequence, the class of `φ.τ₃` is sent to the class of `φ.τ₁`. -/
@[simp]
theorem residueRingEquiv_mk (hS : S.IsAlmostSplit) (φ : S ⟶ S) :
    hS.residueRingEquiv (Ideal.Quotient.mk (Ring.jacobson (End S.X₃)) (.of φ.τ₃)) =
      Ideal.Quotient.mk (Ring.jacobson (End S.X₁)) (.of φ.τ₁) :=
  (Ideal.Quotient.lift_mk _ _ fun _ ↦ hS.residueEndHom_eq_zero_of_mem).trans
    (hS.residueEndHom_of_τ₃ φ)

/-- The inverse of the residue isomorphism sends the class of the first component of an
endomorphism of the almost-split sequence to the class of its third component. -/
@[simp]
theorem residueRingEquiv_symm_mk (hS : S.IsAlmostSplit) (φ : S ⟶ S) :
    hS.residueRingEquiv.symm (Ideal.Quotient.mk (Ring.jacobson (End S.X₁)) (.of φ.τ₁)) =
      Ideal.Quotient.mk (Ring.jacobson (End S.X₃)) (.of φ.τ₃) :=
  (RingEquiv.symm_apply_eq _).mpr (hS.residueRingEquiv_mk φ).symm

section Linear

variable (k : Type*) [CommRing k] [Linear k C]

/-- The residue isomorphism of an almost-split sequence in a `k`-linear category is an isomorphism
of `k`-algebras. -/
noncomputable def residueAlgEquiv (hS : S.IsAlmostSplit) :
    (End S.X₃ ⧸ Ring.jacobson (End S.X₃)) ≃ₐ[k] End S.X₁ ⧸ Ring.jacobson (End S.X₁) :=
  .ofRingEquiv (f := hS.residueRingEquiv) fun c ↦ by
    have h₃ : algebraMap k (End S.X₃) c = .of (c • 𝟙 S).τ₃ := by
      ext; simp [Algebra.algebraMap_eq_smul_one]
    have h₁ : algebraMap k (End S.X₁) c = .of (c • 𝟙 S).τ₁ := by
      ext; simp [Algebra.algebraMap_eq_smul_one]
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, h₃, h₁, residueRingEquiv_mk]

@[simp]
theorem residueAlgEquiv_apply (hS : S.IsAlmostSplit) (x : End S.X₃ ⧸ Ring.jacobson (End S.X₃)) :
    hS.residueAlgEquiv k x = hS.residueRingEquiv x :=
  (rfl)

/-- **The residue division rings of the two end terms of an almost-split sequence have the same
dimension** over the base ring of a linear category. -/
theorem finrank_residue_X₁_eq_finrank_residue_X₃ (hS : S.IsAlmostSplit) :
    finrank k (End S.X₁ ⧸ Ring.jacobson (End S.X₁)) =
      finrank k (End S.X₃ ⧸ Ring.jacobson (End S.X₃)) :=
  (hS.residueAlgEquiv k).toLinearEquiv.finrank_eq.symm

end Linear

/-! ### Over a field: the valued mesh relation -/

section Field

variable (k : Type*) [Field k] [Linear k C]

variable {J : Type*} [Finite J] (P : J → C) [HasBiproduct P] [∀ j, IsLocalRing (End (P j))]

/-- **The valued mesh relation of an almost-split sequence, second half**: in an almost-split
sequence `0 → A → B → C → 0` over a field, with `End C` finite-dimensional and with
`B ≅ ⨁ P` a finite biproduct of objects with local endomorphism rings, for every object `X` with a
local endomorphism ring the first entry of the valuation of `Irr(X, C)` equals the second entry
of the valuation of `Irr(A, X)`. -/
theorem irreducibleMorphismValuation_fst_eq_snd [Module.Finite k (End S.X₃)]
    (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P) (X : C) [IsLocalRing (End X)] :
    (irreducibleMorphismValuation k X S.X₃).1 = (irreducibleMorphismValuation k S.X₁ X).2 := by
  have := hS.isLeftAlmostSplit_f.isLocalRing_end
  have := hS.isRightAlmostSplit_g.isLocalRing_end
  refine Nat.eq_of_mul_eq_mul_left
    (Module.finrank_pos (R := k) (M := End S.X₃ ⧸ Ring.jacobson (End S.X₃))) ?_
  -- Both sides compute the `k`-dimension of `Irr(X, C)`, respectively `Irr(A, X)`, which agree
  -- since both are `dim_k F_X` times the multiplicity of `X` in the middle term.
  calc finrank k (End S.X₃ ⧸ Ring.jacobson (End S.X₃)) * (irreducibleMorphismValuation k X S.X₃).1
      = finrank k ((End X)ᵐᵒᵖ ⧸ Ring.jacobson (End X)ᵐᵒᵖ) *
          (irreducibleMorphismValuation k X S.X₃).2 := by
        rw [finrank_residue_mul_irreducibleMorphismValuation_fst,
          finrank_residueOp_mul_irreducibleMorphismValuation_snd]
    _ = finrank k (End X ⧸ Ring.jacobson (End X)) * (irreducibleMorphismValuation k S.X₁ X).1 := by
        rw [hS.irreducibleMorphismValuation_snd_eq_fst k P e,
          Ring.finrank_quotient_jacobson_mulOpposite]
    _ = finrank k ((End S.X₁)ᵐᵒᵖ ⧸ Ring.jacobson (End S.X₁)ᵐᵒᵖ) *
          (irreducibleMorphismValuation k S.X₁ X).2 := by
        rw [finrank_residue_mul_irreducibleMorphismValuation_fst,
          finrank_residueOp_mul_irreducibleMorphismValuation_snd]
    _ = finrank k (End S.X₃ ⧸ Ring.jacobson (End S.X₃)) *
          (irreducibleMorphismValuation k S.X₁ X).2 := by
        rw [Ring.finrank_quotient_jacobson_mulOpposite,
          hS.finrank_residue_X₁_eq_finrank_residue_X₃ k]

/-- **The valued mesh relation of an almost-split sequence**: under the hypotheses of
`CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_fst_eq_snd`, the valuation
of `Irr(A, X)` is the valuation of `Irr(X, C)` with its two entries exchanged. -/
theorem irreducibleMorphismValuation_X₁_eq_swap [Module.Finite k (End S.X₃)]
    (hS : S.IsAlmostSplit) (e : S.X₂ ≅ ⨁ P) (X : C) [IsLocalRing (End X)] :
    irreducibleMorphismValuation k S.X₁ X = (irreducibleMorphismValuation k X S.X₃).swap :=
  Prod.ext (hS.irreducibleMorphismValuation_snd_eq_fst k P e X).symm
    (hS.irreducibleMorphismValuation_fst_eq_snd k P e X).symm

end Field

end CategoryTheory.ShortComplex.IsAlmostSplit
