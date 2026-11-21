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
# Automorphism products and Weyl groups of direct sums of root pairings

For a finite family of root pairings `P : ∀ c, RootPairing (ι c) R (M c) (N c)`, coordinatewise
automorphisms embed via `RootPairing.piAut`, and this embedding restricts to a multiplicative
isomorphism `RootPairing.piWeylGroupEquiv : (pi P).weylGroup ≃* ∀ c, (P c).weylGroup` matching the
weight-space action and sending each generator `weylGroup.ofIdx (pi P) ⟨c, i⟩` to
`Pi.mulSingle c (weylGroup.ofIdx (P c) i)`.

Transporting along `RootPairing.piEquivInternalDirectSum` yields the corresponding isomorphism
`RootPairing.internalDirectSumWeylGroupEquiv` for finite internal direct sums, equivariant with
respect to `TauCeti.internalProjection`.

## Main definitions

* `RootPairing.piAut`: the canonical monoid embedding `(∀ c, (P c).Aut) →* (pi P).Aut`.
* `RootPairing.piWeylGroupEquiv`: the canonical isomorphism between `(pi P).weylGroup` and
  `∀ c, (P c).weylGroup`.
* `RootPairing.internalDirectSumWeylGroupEquiv`: the canonical isomorphism between
  `(internalDirectSum hEi hEt P).weylGroup` and `∀ c, (P c).weylGroup`.

## Main results

* `RootPairing.piAut_injective`, `RootPairing.piAut_mulSingle_reflection`: properties of the
  product-of-automorphisms embedding.
* `RootPairing.piWeylGroupEquiv_smul`, `RootPairing.piWeylGroupEquiv_ofIdx`: equivariance and
  generator formulas for `RootPairing.piWeylGroupEquiv`.
* `RootPairing.internalProjection_smul_internalDirectSum`,
  `RootPairing.internalDirectSumWeylGroupEquiv_ofIdx_self`,
  `RootPairing.internalDirectSumWeylGroupEquiv_ofIdx_ne`: equivariance and generator formulas for
  `RootPairing.internalDirectSumWeylGroupEquiv`.

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

/-- The canonical embedding of the product of summand automorphism groups into the automorphism
group of `RootPairing.pi P`. -/
noncomputable def piAut : (∀ c, (P c).Aut) →* (pi P).Aut where
  toFun g := Equiv.piCongr (_root_.Equiv.refl κ) g
  map_one' := by
    refine Equiv.weightHom_injective (pi P) (LinearEquiv.ext fun x ↦ funext fun c ↦ ?_)
    have h := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) (1 : ∀ c, (P c).Aut) x c
    simp only [Equiv.weightHom_apply, Equiv.weightEquiv_apply, _root_.Equiv.refl_apply,
      Pi.one_apply] at h ⊢
    rw [h]
    rfl
  map_mul' g h := by
    refine Equiv.weightHom_injective (pi P) (LinearEquiv.ext fun x ↦ funext fun c ↦ ?_)
    simp only [Equiv.weightHom_apply, Equiv.weightEquiv_apply, Equiv.mul_eq_comp,
      Equiv.toHom_comp, Hom.comp, LinearMap.comp_apply]
    have h1 := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) (g * h) x c
    have h2 := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) g
      ((Equiv.piCongr (_root_.Equiv.refl κ) h).weightMap x) c
    have h3 := Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) h x c
    simp only [_root_.Equiv.refl_apply] at h1 h2 h3
    rw [h1, h2, h3]
    rfl

@[simp]
theorem piAut_weightMap_apply (g : ∀ c, (P c).Aut) (x : ∀ c, M c) (c : κ) :
    (piAut P g).weightMap x c = (g c).weightMap (x c) :=
  Equiv.piCongr_weightMap_apply (_root_.Equiv.refl κ) g x c

@[simp]
theorem piAut_coweightMap_apply (g : ∀ c, (P c).Aut) (y : ∀ c, N c) (c : κ) :
    (piAut P g).coweightMap y c = (g c).coweightMap (y c) :=
  Equiv.piCongr_coweightMap_apply (_root_.Equiv.refl κ) g y c

@[simp]
theorem piAut_indexEquiv (g : ∀ c, (P c).Aut) (c : κ) (i : ι c) :
    (piAut P g).indexEquiv ⟨c, i⟩ = ⟨c, (g c).indexEquiv i⟩ :=
  Equiv.piCongr_indexEquiv (_root_.Equiv.refl κ) g c i

/-- `RootPairing.piAut` is injective: an automorphism of `RootPairing.pi P` in its image
determines every coordinate automorphism. -/
theorem piAut_injective : Function.Injective (piAut P) := by
  intro g h hgh
  funext c
  refine Equiv.weightHom_injective (P c) (LinearEquiv.ext fun x ↦ ?_)
  have h1 := congrFun (congrArg (fun a : (pi P).Aut ↦ a.weightMap (Pi.single c x)) hgh) c
  simpa using h1

/-- Inserting a single reflection at coordinate `c` maps under `piAut` to the reflection of the
direct sum at `⟨c, i⟩`. -/
@[simp]
theorem piAut_mulSingle_reflection (c : κ) (i : ι c) :
    piAut P (Pi.mulSingle c (Equiv.reflection (P c) i)) = Equiv.reflection (pi P) ⟨c, i⟩ := by
  refine Equiv.weightHom_injective (pi P) (LinearEquiv.ext fun x ↦ funext fun d ↦ ?_)
  by_cases h : d = c
  · subst h
    simp only [Equiv.weightHom_apply, Equiv.weightEquiv_apply, piAut_weightMap_apply,
      Pi.mulSingle_eq_same, Equiv.reflection_weightEquiv, pi_reflection_apply_same]
    exact LinearEquiv.congr_fun (Equiv.reflection_weightEquiv (P d) i) (x d)
  · simp [Equiv.weightHom_apply, Equiv.reflection_weightEquiv, h]

/-- Each single-coordinate Weyl-group element lands in `(pi P).weylGroup` under `piAut`. -/
private theorem piAut_mulSingle_mem_weylGroup (c : κ) {a : (P c).Aut} (ha : a ∈ (P c).weylGroup) :
    piAut P (Pi.mulSingle c a) ∈ (pi P).weylGroup := by
  induction ha using weylGroup.induction with
  | mem i =>
    rw [piAut_mulSingle_reflection]
    exact Subgroup.subset_closure ⟨⟨c, i⟩, rfl⟩
  | one =>
    rw [Pi.mulSingle_one, map_one]
    exact (pi P).weylGroup.one_mem
  | mul a b _ _ ha hb =>
    rw [Pi.mulSingle_mul, map_mul]
    exact (pi P).weylGroup.mul_mem ha hb

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
      rintro ⟨g, hg⟩
      induction hg using weylGroup.induction with
      | mem s =>
        rcases s with ⟨c, i⟩
        let w : ∀ d, (P d).weylGroup := Pi.mulSingle c (weylGroup.ofIdx (P c) i)
        refine ⟨w, Subtype.ext ?_⟩
        have hval : (fun d ↦ (w d : (P d).Aut)) = Pi.mulSingle c (Equiv.reflection (P c) i) := by
          funext d
          by_cases h : d = c
          · subst h; simp [w]
          · simp [w, Pi.mulSingle_eq_of_ne h]
        simp [piWeylGroupHom, hval]
      | one => exact ⟨1, map_one _⟩
      | mul a b _ _ iha ihb =>
        rcases iha with ⟨wa, hwa⟩
        rcases ihb with ⟨wb, hwb⟩
        exact ⟨wa * wb, by rw [map_mul, hwa, hwb]; rfl⟩⟩).symm

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
  funext d
  by_cases h : d = c
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h]

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

end Internal

end RootPairing
