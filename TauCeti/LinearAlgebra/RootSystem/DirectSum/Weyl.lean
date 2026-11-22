/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport
import Mathlib.Algebra.Group.Submonoid.Finite

/-!
# Weyl groups of direct sums of root pairings

For a finite family of root pairings `P : ∀ c, RootPairing (ι c) R (M c) (N c)`, the product-of-
automorphisms embedding `RootPairing.piAut` restricts to a multiplicative isomorphism
`RootPairing.piWeylGroupEquiv : (pi P).weylGroup ≃* ∀ c, (P c).weylGroup` matching the
weight-space action and sending each generator `weylGroup.ofIdx (pi P) ⟨c, i⟩` to
`Pi.mulSingle c (weylGroup.ofIdx (P c) i)`.

Transporting along `RootPairing.piEquivInternalDirectSum` yields the corresponding isomorphism
`RootPairing.internalDirectSumWeylGroupEquiv` for finite internal direct sums, equivariant with
respect to `TauCeti.internalProjection`.

## Main definitions

* `RootPairing.piWeylGroupEquiv`: the canonical isomorphism between `(pi P).weylGroup` and
  `∀ c, (P c).weylGroup`.
* `RootPairing.internalDirectSumWeylGroupEquiv`: the canonical isomorphism between
  `(internalDirectSum hEi hEt P).weylGroup` and `∀ c, (P c).weylGroup`.

## Main results

* `RootPairing.piWeylGroupEquiv_smul`, `RootPairing.piWeylGroupEquiv_ofIdx`,
  `RootPairing.piWeylGroupEquiv_symm_mulSingle_ofIdx`: equivariance and generator formulas for
  `RootPairing.piWeylGroupEquiv`.
* `RootPairing.internalProjection_smul_internalDirectSum`,
  `RootPairing.internalDirectSumWeylGroupEquiv_ofIdx_self`,
  `RootPairing.internalDirectSumWeylGroupEquiv_ofIdx_ne`,
  `RootPairing.internalDirectSumWeylGroupEquiv_symm_mulSingle_ofIdx`: equivariance and generator
  formulas for `RootPairing.internalDirectSumWeylGroupEquiv`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2, Proposition 5.
-/

public section

open TauCeti

namespace RootPairing

section External

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (M c) (N c))

/-- Each single-coordinate Weyl-group element lands in `(pi P).weylGroup` under `piAut`. -/
private theorem piAut_mulSingle_mem_weylGroup (c : κ) {a : (P c).Aut} (ha : a ∈ (P c).weylGroup) :
    piAut P (Pi.mulSingle c a) ∈ (pi P).weylGroup := by
  have hle : (P c).weylGroup ≤
      (pi P).weylGroup.comap ((piAut P).comp (MonoidHom.mulSingle (fun d ↦ (P d).Aut) c)) := by
    rw [weylGroup, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    simp [reflection_mem_weylGroup]
  exact hle ha

/-- Every product of summand Weyl-group elements lands in `(pi P).weylGroup` under `piAut`. -/
private theorem piAut_mem_weylGroup (w : ∀ c, (P c).weylGroup) :
    piAut P (fun c ↦ (w c : (P c).Aut)) ∈ (pi P).weylGroup :=
  Submonoid.pi_mem_of_mulSingle_mem (H := ((pi P).weylGroup.comap (piAut P)).toSubmonoid)
    (fun c ↦ (w c : (P c).Aut)) fun c ↦ piAut_mulSingle_mem_weylGroup P c (w c).property

/-- The homomorphism `(∀ c, (P c).weylGroup) →* (pi P).weylGroup` induced by `piAut`. -/
private noncomputable def piWeylGroupHom : (∀ c, (P c).weylGroup) →* (pi P).weylGroup where
  toFun w := ⟨piAut P fun c ↦ (w c : (P c).Aut), piAut_mem_weylGroup P w⟩
  map_one' := Subtype.ext (map_one (piAut P))
  map_mul' _ _ := Subtype.ext (map_mul (piAut P) _ _)

/-- **The Weyl group of a finite direct sum is canonically isomorphic to the product of the
Weyl groups of its summands.** -/
noncomputable def piWeylGroupEquiv : (pi P).weylGroup ≃* ∀ c, (P c).weylGroup :=
  (MulEquiv.ofBijective (piWeylGroupHom P)
    ⟨fun _ _ h ↦ funext fun c ↦ Subtype.ext
        (congrFun (piAut_injective P (congrArg Subtype.val h)) c),
     by
      have hle : (pi P).weylGroup ≤
          ((pi P).weylGroup.subtype.comp (piWeylGroupHom P)).range := by
        conv_lhs => rw [weylGroup]
        rw [Subgroup.closure_le]
        rintro _ ⟨⟨c, i⟩, rfl⟩
        let w : ∀ d, (P d).weylGroup := Pi.mulSingle c (weylGroup.ofIdx (P c) i)
        refine ⟨w, ?_⟩
        have hval : (fun d ↦ (w d : (P d).Aut)) =
            Pi.mulSingle c (Equiv.reflection (P c) i) :=
          (Pi.mulSingle_op (fun d ↦ ⇑(P d).weylGroup.subtype) (fun _ ↦ map_one _) c
            (weylGroup.ofIdx (P c) i)).symm
        simp [piWeylGroupHom, hval]
      rintro ⟨g, hg⟩
      obtain ⟨w, hw⟩ := hle hg
      exact ⟨w, Subtype.ext hw⟩⟩).symm

@[simp]
theorem coe_piWeylGroupEquiv_symm (w : ∀ c, (P c).weylGroup) :
    ((piWeylGroupEquiv P).symm w : (pi P).Aut) = piAut P fun c ↦ (w c : (P c).Aut) :=
  (rfl)

theorem piWeylGroupEquiv_symm_smul (w : ∀ c, (P c).weylGroup) (x : ∀ c, M c) (c : κ) :
    ((piWeylGroupEquiv P).symm w • x) c = w c • x c :=
  piAut_weightMap_apply P (fun d ↦ (w d : (P d).Aut)) x c

@[simp]
theorem piWeylGroupEquiv_smul (w : (pi P).weylGroup) (x : ∀ c, M c) (c : κ) :
    (w • x) c = piWeylGroupEquiv P w c • x c := by
  simpa using piWeylGroupEquiv_symm_smul P (piWeylGroupEquiv P w) x c

/-- The Weyl-group isomorphism matches each reflection of the direct sum with the single-coordinate
reflection in the product of Weyl groups. -/
@[simp]
theorem piWeylGroupEquiv_ofIdx (c : κ) (i : ι c) :
    piWeylGroupEquiv P (weylGroup.ofIdx (pi P) ⟨c, i⟩) =
      Pi.mulSingle c (weylGroup.ofIdx (P c) i) := by
  refine (piWeylGroupEquiv P).symm.injective ?_
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [coe_piWeylGroupEquiv_symm, weylGroup.coe_ofIdx]
  refine (piAut_mulSingle_reflection P c i).symm.trans ?_
  congr 1
  exact Pi.mulSingle_op (fun d ↦ ⇑(P d).weylGroup.subtype) (fun _ ↦ map_one _) c
    (weylGroup.ofIdx (P c) i)

/-- Lifting a single summand reflection from coordinate `c` maps under `piWeylGroupEquiv.symm`
to the direct-sum reflection at `⟨c, i⟩`. -/
@[simp]
theorem piWeylGroupEquiv_symm_mulSingle_ofIdx (c : κ) (i : ι c) :
    (piWeylGroupEquiv P).symm (Pi.mulSingle c (weylGroup.ofIdx (P c) i)) =
      weylGroup.ofIdx (pi P) ⟨c, i⟩ :=
  (piWeylGroupEquiv P).symm_apply_eq.mpr (piWeylGroupEquiv_ofIdx P c i).symm

end External

section Internal

variable {κ R M : Type*} [Finite κ] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (E c) (N c))

/-- **The Weyl group of a finite internal direct sum is canonically isomorphic to the product of
the Weyl groups of its summands.** -/
noncomputable def internalDirectSumWeylGroupEquiv :
    (internalDirectSum hEi hEt P).weylGroup ≃* ∀ c, (P c).weylGroup :=
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  (piEquivInternalDirectSum hEi hEt P).weylGroupEquiv.symm.trans (piWeylGroupEquiv P)

/-- The Weyl-group isomorphism acts equivariantly on every internal projection. -/
@[simp]
theorem internalProjection_smul_internalDirectSum
    (w : (internalDirectSum hEi hEt P).weylGroup) (c : κ) (x : M) :
    internalProjection hEi hEt c (w • x) =
      internalDirectSumWeylGroupEquiv hEi hEt P w c • internalProjection hEi hEt c x := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  let e := piEquivInternalDirectSum hEi hEt P
  have h := e.weylGroupEquiv_smul (e.weylGroupEquiv.symm w) (e.weightEquiv.symm x)
  rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  have h' := congrFun (congrArg e.weightEquiv.symm h) c
  rw [LinearEquiv.symm_apply_apply] at h'
  simpa [internalDirectSumWeylGroupEquiv, e] using h'

@[simp]
theorem internalDirectSumWeylGroupEquiv_ofIdx_self (c : κ) (i : ι c) :
    internalDirectSumWeylGroupEquiv hEi hEt P
        (weylGroup.ofIdx (internalDirectSum hEi hEt P) ⟨c, i⟩) c =
      weylGroup.ofIdx (P c) i := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp [internalDirectSumWeylGroupEquiv]

@[simp]
theorem internalDirectSumWeylGroupEquiv_ofIdx_ne {c d : κ} (hdc : d ≠ c) (i : ι c) :
    internalDirectSumWeylGroupEquiv hEi hEt P
        (weylGroup.ofIdx (internalDirectSum hEi hEt P) ⟨c, i⟩) d = 1 := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  simp [internalDirectSumWeylGroupEquiv, hdc]

/-- Lifting a single summand reflection from coordinate `c` maps under
`internalDirectSumWeylGroupEquiv.symm` to the internal direct-sum reflection at `⟨c, i⟩`. -/
@[simp]
theorem internalDirectSumWeylGroupEquiv_symm_mulSingle_ofIdx [DecidableEq κ]
    (c : κ) (i : ι c) :
    (internalDirectSumWeylGroupEquiv hEi hEt P).symm
        (Pi.mulSingle c (weylGroup.ofIdx (P c) i)) =
      weylGroup.ofIdx (internalDirectSum hEi hEt P) ⟨c, i⟩ := by
  let _ : Fintype κ := Fintype.ofFinite κ
  rw [MulEquiv.symm_apply_eq]
  ext d
  by_cases hdc : d = c
  · subst hdc
    simp
  · simp [hdc]

end Internal

end RootPairing
