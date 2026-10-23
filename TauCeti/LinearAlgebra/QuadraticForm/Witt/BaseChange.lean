/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.FundamentalIdeal
public import TauCeti.RingTheory.Ideal.Operations

/-!
# Base change of Witt theory

Scalar extension preserves the hyperbolic class, so the Witt index cannot decrease under a field
extension.  It is unchanged when the anisotropic part remains anisotropic after base change.
It also induces ring homomorphisms on Witt-Grothendieck and Witt rings that preserve dimension
modulo two and every power of the fundamental ideal.

## Main results

* `TauCeti.RegularFormClass.baseChange_wittDecomposition`: base change of the Witt decomposition.
* `TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange`: the Witt index cannot decrease.
* `TauCeti.RegularFormClass.wittIndex_baseChange_eq_iff`: the index is unchanged exactly when the
  extended anisotropic part is anisotropic.
* `QuadraticForm.wittIndex_le_wittIndex_baseChange`: the corresponding inequality for a regular
  quadratic form.
* `QuadraticForm.wittIndex_baseChange_eq_iff`: the corresponding equivalence for a regular
  quadratic form.
* `TauCeti.WittGrothendieckRing.baseChange` and `TauCeti.WittRing.baseChange`: scalar extension
  as ring homomorphisms, with identity and tower laws.
* `TauCeti.WittRing.baseChange_mk`: compatibility with the Witt-ring quotient map.
* `TauCeti.WittRing.baseChange_oneFoldPfisterClass`: compatibility with one-fold Pfister classes.
* `TauCeti.WittRing.map_fundamentalIdeal_pow_le`: compatibility with the fundamental ideal
  filtration.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §1.
* W. Scharlau, *Quadratic and Hermitian Forms* (1985), Chapter 2, §5.
-/

public section
noncomputable section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

variable [Invertible (2 : K)]

/-- Base change of the Witt decomposition: the extended class is the same number of hyperbolic
planes plus the extended anisotropic part. -/
theorem RegularFormClass.baseChange_wittDecomposition (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    c.baseChange L =
      RegularFormClass.wittIndex c • hyperbolicClass L + c.anisotropicPart.baseChange L := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  conv_lhs => rw [RegularFormClass.wittDecomposition c]
  rw [RegularFormClass.baseChange_add, RegularFormClass.baseChange_nsmul,
    RegularFormClass.baseChange_hyperbolicClass]

/-! ### Witt index -/

/-- The Witt index cannot decrease after extending the base field. -/
theorem RegularFormClass.wittIndex_le_wittIndex_baseChange (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.wittIndex c ≤ RegularFormClass.wittIndex (c.baseChange L) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [RegularFormClass.baseChange_wittDecomposition,
    RegularFormClass.wittIndex_nsmul_hyperbolicClass_add]
  exact Nat.le_add_right _ _

/-- The anisotropic part commutes with base change when its base change remains anisotropic. -/
theorem RegularFormClass.anisotropicPart_baseChange (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.Anisotropic (c.anisotropicPart.baseChange L) →
      RegularFormClass.anisotropicPart (c.baseChange L) = c.anisotropicPart.baseChange L := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  exact fun ha ↦ RegularFormClass.anisotropicPart_eq ha c.baseChange_wittDecomposition

/-- The Witt index is unchanged after base change exactly when the extended anisotropic part
remains anisotropic. -/
theorem RegularFormClass.wittIndex_baseChange_eq_iff (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.wittIndex (c.baseChange L) = RegularFormClass.wittIndex c ↔
      RegularFormClass.Anisotropic (c.anisotropicPart.baseChange L) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [RegularFormClass.baseChange_wittDecomposition,
    RegularFormClass.wittIndex_nsmul_hyperbolicClass_add]
  constructor
  · intro h
    rw [← RegularFormClass.wittIndex_eq_zero_iff]
    omega
  · intro ha
    have hzero := RegularFormClass.wittIndex_eq_zero_iff.mpr ha
    omega

end TauCeti

namespace QuadraticForm

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [Invertible (2 : K)]

/-- The Witt index of a regular quadratic form cannot decrease after extending scalars. -/
theorem wittIndex_le_wittIndex_baseChange {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.RegularFormClass.wittIndex (TauCeti.formClass Q hQ) ≤
      TauCeti.RegularFormClass.wittIndex
        (TauCeti.formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [Q.formClass_baseChange hQ]
  exact TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange _

/-- The Witt index of a regular quadratic form is unchanged after extending scalars exactly when
the extended anisotropic part remains anisotropic. -/
theorem wittIndex_baseChange_eq_iff {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.RegularFormClass.wittIndex
        (TauCeti.formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) =
      TauCeti.RegularFormClass.wittIndex (TauCeti.formClass Q hQ) ↔
        TauCeti.RegularFormClass.Anisotropic
          ((TauCeti.formClass Q hQ).anisotropicPart.baseChange L) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [Q.formClass_baseChange hQ]
  exact TauCeti.RegularFormClass.wittIndex_baseChange_eq_iff _

end QuadraticForm

namespace TauCeti

variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [Field L] [Field M] [Algebra K L]
variable [Invertible (2 : K)] [Invertible (2 : L)]

/-- Scalar extension of a Witt-Grothendieck class, induced by scalar extension of forms. -/
def WittGrothendieckRing.baseChange : WittGrothendieckRing K →+* WittGrothendieckRing L :=
  (WittGrothendieckRing.equivGrothendieck (K := L)).symm.toRingHom.comp
    ((Algebra.GrothendieckAddGroup.liftRingHom
      (Algebra.GrothendieckAddGroup.ofRingHom.comp
        (RegularFormClass.baseChangeHom (K := K) (L := L)))).comp
          (WittGrothendieckRing.equivGrothendieck (K := K)).toRingHom)

/-- Extending the Grothendieck class of a form extends that form's class. -/
@[simp]
theorem WittGrothendieckRing.baseChange_toWittGrothendieck (x : RegularFormClass K) :
    WittGrothendieckRing.baseChange (L := L) (toWittGrothendieck x) =
      toWittGrothendieck (RegularFormClass.baseChange L x) := by
  apply (WittGrothendieckRing.equivGrothendieck (K := L)).injective
  simp only [WittGrothendieckRing.baseChange, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply,
    toWittGrothendieck_apply, Algebra.GrothendieckAddGroup.liftRingHom_apply_of,
    Algebra.GrothendieckAddGroup.ofRingHom_apply, RegularFormClass.baseChangeHom_apply]

/-- Scalar extension to the same field is the identity Witt-Grothendieck ring homomorphism. -/
@[simp]
theorem WittGrothendieckRing.baseChange_self :
    WittGrothendieckRing.baseChange (K := K) (L := K) = RingHom.id _ := by
  ext x
  obtain ⟨a, b, rfl⟩ := exists_eq_sub_toWittGrothendieck x
  simp

/-- Scalar extension of virtual forms preserves their integer rank. -/
@[simp]
theorem WittGrothendieckRing.rank_baseChange (x : WittGrothendieckRing K) :
    WittGrothendieckRing.rank (WittGrothendieckRing.baseChange (L := L) x) =
      WittGrothendieckRing.rank x := by
  obtain ⟨a, b, rfl⟩ := exists_eq_sub_toWittGrothendieck x
  simp

/-- Scalar extension carries the ideal generated by the hyperbolic plane into the corresponding
ideal over the extension field. -/
theorem WittGrothendieckRing.baseChange_mem_hyperbolicIdeal
    {x : WittGrothendieckRing K} (hx : x ∈ hyperbolicIdeal K) :
    WittGrothendieckRing.baseChange (L := L) x ∈ hyperbolicIdeal L := by
  obtain ⟨n, rfl⟩ := mem_hyperbolicIdeal_iff.mp hx
  have hhyper : RegularFormClass.baseChange L (hyperbolicClass K) = hyperbolicClass L := by
    have hinst : ((Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm) =
        (inferInstance : Invertible (2 : L)) := Subsingleton.elim _ _
    exact (RegularFormClass.baseChange_hyperbolicClass (K := K) (L := L)).trans
      (congrArg (fun i : Invertible (2 : L) => @hyperbolicClass L _ i) hinst)
  rw [map_zsmul, baseChange_toWittGrothendieck, hhyper]
  have h : toWittGrothendieck (hyperbolicClass L) ∈ hyperbolicIdeal L := by
    apply mem_hyperbolicIdeal_iff.mpr
    refine ⟨1, ?_⟩
    simp
  simpa only [Submodule.mem_toAddSubgroup] using
    AddSubgroup.zsmul_mem (hyperbolicIdeal L).toAddSubgroup h n

/-- Scalar extension of Witt classes as a ring homomorphism. -/
def WittRing.baseChange : WittRing K →+* WittRing L :=
  WittRing.lift ((WittRing.mk (K := L)).comp WittGrothendieckRing.baseChange) <| by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, WittRing.mk_eq_zero_iff_mem]
    exact WittGrothendieckRing.baseChange_mem_hyperbolicIdeal hx

/-- Scalar extension commutes with the quotient map to the Witt ring. -/
@[simp]
theorem WittRing.baseChange_mk (x : WittGrothendieckRing K) :
    WittRing.baseChange (L := L) (WittRing.mk x) =
      WittRing.mk (WittGrothendieckRing.baseChange (L := L) x) := by
  rw [← RingHom.comp_apply, WittRing.baseChange, WittRing.lift_comp_mk, RingHom.comp_apply]

/-- Extending the Witt class of a form gives the Witt class of its scalar extension. -/
@[simp]
theorem WittRing.baseChange_wittClass (x : RegularFormClass K) :
    WittRing.baseChange (L := L) (wittClass x) =
      wittClass (RegularFormClass.baseChange L x) := by
  rw [wittClass_apply, wittClass_apply, WittRing.baseChange_mk,
    WittGrothendieckRing.baseChange_toWittGrothendieck]

/-- Scalar extension carries a one-fold Pfister class to the class of the mapped unit. -/
@[simp]
theorem WittRing.baseChange_oneFoldPfisterClass (a : Kˣ) :
    WittRing.baseChange (L := L) (oneFoldPfisterClass a) =
      oneFoldPfisterClass (Units.map (algebraMap K L).toMonoidHom a) := by
  rw [oneFoldPfisterClass_eq, oneFoldPfisterClass_eq, map_add, map_one,
    WittRing.baseChange_wittClass, RegularFormClass.baseChange_mk]
  congr 1
  apply congrArg wittClass
  refine congrArg (Quotient.mk (regularFormSetoid L))
    (RegularFormPresentation.ext (by simp) fun i ↦ ?_)
  apply Units.ext
  simp

/-- Scalar extension to the same field is the identity Witt ring homomorphism. -/
@[simp]
theorem WittRing.baseChange_self :
    WittRing.baseChange (K := K) (L := K) = RingHom.id _ := by
  ext x
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  simp

variable [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Invertible (2 : M)]

/-- Scalar extension through a tower agrees with direct extension on Witt-Grothendieck rings. -/
@[simp]
theorem WittGrothendieckRing.baseChange_baseChange_apply (x : WittGrothendieckRing K) :
    WittGrothendieckRing.baseChange (L := M)
        (WittGrothendieckRing.baseChange (L := L) x) =
      WittGrothendieckRing.baseChange (L := M) x := by
  obtain ⟨a, b, rfl⟩ := exists_eq_sub_toWittGrothendieck x
  simp

/-- Scalar extension through a tower composes as Witt-Grothendieck ring homomorphisms. -/
@[simp]
theorem WittGrothendieckRing.baseChange_comp :
    (WittGrothendieckRing.baseChange (K := L) (L := M)).comp
      (WittGrothendieckRing.baseChange (K := K) (L := L)) =
        WittGrothendieckRing.baseChange (K := K) (L := M) := by
  ext x
  simp

/-- Extending Witt classes through a tower agrees with direct scalar extension. -/
@[simp]
theorem WittRing.baseChange_baseChange_apply (x : WittRing K) :
    WittRing.baseChange (L := M) (WittRing.baseChange (L := L) x) =
      WittRing.baseChange (L := M) x := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  simp

/-- Scalar extension through a tower composes as Witt ring homomorphisms. -/
@[simp]
theorem WittRing.baseChange_comp :
    (WittRing.baseChange (K := L) (L := M)).comp
      (WittRing.baseChange (K := K) (L := L)) =
        WittRing.baseChange (K := K) (L := M) := by
  ext x
  simp

/-! ### Fundamental ideal -/

/-- Scalar extension preserves the dimension of a Witt class modulo two. -/
@[simp]
theorem WittRing.dimMod2_baseChange (x : WittRing K) :
    WittRing.dimMod2 (WittRing.baseChange (L := L) x) = WittRing.dimMod2 x := by
  obtain ⟨q, rfl⟩ := wittClass_surjective x
  simp

/-- Scalar extension sends the fundamental ideal into the fundamental ideal. -/
theorem WittRing.baseChange_mem_fundamentalIdeal {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K) :
    WittRing.baseChange (L := L) x ∈ fundamentalIdeal L := by
  rwa [mem_fundamentalIdeal_iff, dimMod2_baseChange, ← mem_fundamentalIdeal_iff]

/-- Scalar extension maps the fundamental ideal into the fundamental ideal. -/
theorem WittRing.map_fundamentalIdeal_le :
    (fundamentalIdeal K).map (WittRing.baseChange (L := L)) ≤ fundamentalIdeal L :=
  Ideal.map_le_iff_le_comap.mpr fun _ hx => WittRing.baseChange_mem_fundamentalIdeal hx

/-- Scalar extension maps every power of the fundamental ideal into the corresponding power. -/
theorem WittRing.map_fundamentalIdeal_pow_le (n : ℕ) :
    (fundamentalIdeal K ^ n).map (WittRing.baseChange (L := L)) ≤
      fundamentalIdeal L ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (WittRing.map_fundamentalIdeal_le (K := K) (L := L)) n

/-- Scalar extension sends every power of the fundamental ideal into the corresponding power.
This is the filtration compatibility used by the Witt ring's cohomological invariants. -/
theorem WittRing.baseChange_mem_fundamentalIdeal_pow (n : ℕ) {x : WittRing K}
    (hx : x ∈ fundamentalIdeal K ^ n) :
    WittRing.baseChange (L := L) x ∈ fundamentalIdeal L ^ n := by
  exact WittRing.map_fundamentalIdeal_pow_le n (Ideal.mem_map_of_mem _ hx)

end TauCeti
