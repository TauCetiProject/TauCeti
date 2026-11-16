/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Invariant forms on simply laced root systems

In a simply laced root system all roots in the same irreducible component have the same squared
length for every invariant form; when the root system is irreducible all roots have the same length,
and two roots whose sum is again a root have Cartan integer `-1`.

Over a characteristic-zero field, rescaling the canonical root form `P.toInvariantForm` on each
irreducible component to take value `2` on a representative root yields an intrinsic invariant form
`RootPairing.simplyLacedForm`. Whenever `P` admits a simply laced base, `P.simplyLacedForm` takes
value `2` on every root, identifies pairing against `αᵢ` with the coroot functional `αᵢ^∨`, is the
unique invariant form with `B(αᵢ, αᵢ) = 2` for all `i`, and is preserved by every root-pairing
morphism.

## Main definitions

* `RootPairing.simplyLacedForm`: the component-normalized invariant form on a finite
  crystallographic root system over a characteristic-zero field.

## Main results

* `RootPairing.InvariantForm.apply_root_root_eq_of_componentOf_eq`: in a simply laced root system,
  two roots in the same irreducible component have the same squared length for every invariant form.
* `RootPairing.InvariantForm.apply_root_root_eq_of_isSimplyLaced`: in a simply laced irreducible
  root system all roots have the same length.
* `RootPairing.Base.pairingIn_eq_neg_one_of_isSimplyLaced`: two roots whose sum is a root have
  Cartan integer `-1`.
* `RootPairing.simplyLacedForm_root_self`, `RootPairing.simplyLacedForm_apply_root`,
  `RootPairing.eq_simplyLacedForm_of_root_self`: `P.simplyLacedForm` takes value `2` on every root
  of a simply laced root system, matches `P.coroot'` against roots, and is uniquely determined by
  this normalization.
* `RootPairing.InvariantForm.comap_simplyLacedForm` and `RootPairing.Hom.simplyLacedForm_weightMap`:
  root-pairing morphisms into a simply laced root system preserve `simplyLacedForm`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, no. 4.
-/

public section

open TauCeti (diagramGraph diagramGraph_adj preconnected_diagramGraph_cartanMatrix)

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- Along a walk in `diagramGraph b.cartanMatrix` of a simply laced base `b`, any invariant form
assigns equal squared lengths to the simple roots. -/
private theorem apply_simpleRoot_eq_of_reachable [P.IsCrystallographic] (B : P.InvariantForm)
    (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced) {u v : b.support}
    (h : (diagramGraph b.cartanMatrix).Reachable u v) :
    B.form (P.root u) (P.root u) = B.form (P.root v) (P.root v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | @cons a c d hadj _ ih =>
    rw [← ih]
    obtain ⟨hne, hmat, hmat'⟩ := diagramGraph_adj.mp hadj
    have hac : b.cartanMatrix a c = -1 := (hsl hne).resolve_left hmat
    have hca : b.cartanMatrix c a = -1 := (hsl hne.symm).resolve_left hmat'
    have hp (x y : b.support) (hxy : b.cartanMatrix x y = -1) : P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hxy
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    have hswap := B.pairing_mul_eq_pairing_mul_swap (a : ι) c
    rw [hp c a hca, hp a c hac] at hswap
    linear_combination -hswap

/-- Every root `k` has the same squared length under `B` as a simple root in its irreducible
component. -/
private theorem exists_mem_support_apply_root_eq [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] (B : P.InvariantForm) (b : P.Base) (k : ι) :
    ∃ s : b.support, P.componentOf (s : ι) = P.componentOf k ∧
      B.form (P.root k) (P.root k) = B.form (P.root s) (P.root s) := by
  refine b.induction_reflect k
    (p := fun k ↦ ∃ s : b.support, P.componentOf (s : ι) = P.componentOf k ∧
      B.form (P.root k) (P.root k) = B.form (P.root s) (P.root s))
    (fun i ⟨s, hcomp, hlen⟩ ↦ ⟨s, hcomp.trans (componentOf_reflectionPerm i i).symm, by
      rw [root_reflectionPerm, B.apply_reflection_reflection, hlen]⟩)
    (fun i hi ↦ ⟨⟨i, hi⟩, rfl, rfl⟩)
    (fun i j ⟨s, hcomp, hlen⟩ _ ↦ ⟨s, hcomp.trans (componentOf_reflectionPerm j i).symm, by
      rw [root_reflectionPerm, B.apply_reflection_reflection, hlen]⟩)

/-- **In a simply laced root system, two roots in the same irreducible component have the same
squared length** for every invariant form. Different irreducible components may carry different
scales, as on `A₁ × A₁`. -/
theorem InvariantForm.apply_root_root_eq_of_componentOf_eq [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) {i j : ι} (hij : P.componentOf i = P.componentOf j) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  obtain ⟨s₁, hc₁, hl₁⟩ := exists_mem_support_apply_root_eq B b i
  obtain ⟨s₂, hc₂, hl₂⟩ := exists_mem_support_apply_root_eq B b j
  have hreach : P.nonorthogonalGraph.Reachable (s₁ : ι) (s₂ : ι) :=
    SimpleGraph.ConnectedComponent.exact (hc₁.trans (hij.trans hc₂.symm))
  rw [hl₁, hl₂]
  exact apply_simpleRoot_eq_of_reachable B b hsl (b.reachable_nonorthogonalGraph_iff.mp hreach)

/-- **In a simply laced irreducible root system all roots have the same length** for every invariant
form. Irreducibility is needed: a system of type `A₁ × A₁` has invariant forms giving its two
components different lengths. -/
theorem InvariantForm.apply_root_root_eq_of_isSimplyLaced [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  obtain ⟨s₁, hs₁, hc₁⟩ := b.exists_mem_support_componentOf_eq i
  obtain ⟨s₂, hs₂, hc₂⟩ := b.exists_mem_support_componentOf_eq j
  refine B.apply_root_root_eq_of_componentOf_eq b hsl (hc₁.symm.trans ?_)
  refine (SimpleGraph.ConnectedComponent.sound ?_).trans hc₂
  exact b.reachable_nonorthogonalGraph_iff.mpr
    (preconnected_diagramGraph_cartanMatrix b ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩)

namespace Base

variable [CharZero R] (b : P.Base) [P.IsCrystallographic] [Finite ι] [IsDomain R] [P.IsReduced]
  [P.IsIrreducible]

/-- **In a simply laced irreducible root system, two roots whose sum is a root have Cartan integer
`-1`.** -/
theorem pairingIn_eq_neg_one_of_isSimplyLaced (hsl : b.cartanMatrix.IsSimplyLaced) {i k m : ι}
    (hm : P.root m = P.root i + P.root k) : P.pairingIn ℤ i k = -1 := by
  have := Fintype.ofFinite ι
  let B := P.toInvariantForm
  have hlen (x y : ι) := B.apply_root_root_eq_of_isSimplyLaced b hsl x y
  have hexp := B.form_root_add_root_self k i
  rw [add_comm (P.root k), ← hm, hlen m k, hlen i k] at hexp
  have hz : (P.pairing i k + 1) * B.form (P.root k) (P.root k) = 0 := by
    linear_combination -hexp
  have hp : P.pairing i k = -1 := by
    have := (mul_eq_zero.mp hz).resolve_right (B.ne_zero k)
    linear_combination this
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [algebraMap_pairingIn, hp, map_neg, map_one]

end Base

end CommRing

/-! ### Component-normalized invariant form -/

section Field

variable {ι K M N : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem]
  [P.IsCrystallographic]

/-- **Component-normalized invariant form.** Rescales `P.toInvariantForm` on each irreducible
component so that a representative root of that component has squared length `2`. When `P` is
reduced and admits a base `b` with `b.cartanMatrix.IsSimplyLaced`, every root has squared length `2`
(`RootPairing.simplyLacedForm_root_self`), making `P.simplyLacedForm` the unique invariant form with
`B(αᵢ, αᵢ) = 2` for all `i` (`RootPairing.eq_simplyLacedForm_of_root_self`), independent of `b` and
of the component representatives. -/
noncomputable def simplyLacedForm : P.InvariantForm :=
  letI := Fintype.ofFinite ι
  InvariantForm.ofComponent fun C ↦
    Units.mk0
      (2 / P.toInvariantForm.form
        (P.root C.nonempty_supp.some) (P.root C.nonempty_supp.some))
      (div_ne_zero two_ne_zero (P.toInvariantForm.ne_zero _)) •
    P.toInvariantForm.restrictComponent C

/-- Over a linearly ordered field, `P.simplyLacedForm` is positive definite. -/
theorem posDef_simplyLacedForm [LinearOrder K] [IsStrictOrderedRing K] :
    P.simplyLacedForm.form.toQuadraticMap.PosDef := by
  let _ := Fintype.ofFinite ι
  rw [simplyLacedForm, InvariantForm.posDef_ofComponent_iff]
  intro C x hx
  have hscale : 0 < 2 / P.toInvariantForm.form
      (P.root C.nonempty_supp.some) (P.root C.nonempty_supp.some) :=
    div_pos two_pos (P.rootForm_posDef _ (P.ne_zero _))
  simpa using mul_pos hscale
    (InvariantForm.posDef_restrictComponent (B := P.toInvariantForm) P.rootForm_posDef C x hx)

/-- Uniqueness of `P.simplyLacedForm`: any invariant form taking value `2` on every root equals
`P.simplyLacedForm`. -/
theorem eq_simplyLacedForm_of_root_self {B : P.InvariantForm}
    (hB : ∀ i, B.form (P.root i) (P.root i) = 2) :
    B = P.simplyLacedForm := by
  let _ := Fintype.ofFinite ι
  refine (InvariantForm.componentEquiv (P := P)).injective (funext fun C ↦ ?_)
  let i₀ := C.nonempty_supp.some
  have hcomp : P.componentOf i₀ = C := (C.mem_supp_iff i₀).mp C.nonempty_supp.some_mem
  have hi₀ : P.root i₀ ∈ P.componentSpace C :=
    root_mem_componentSpace_of_mem_supp C.nonempty_supp.some_mem
  have hslf : P.simplyLacedForm.form (P.root i₀) (P.root i₀) = 2 := by
    rw [simplyLacedForm, InvariantForm.ofComponent_form_apply_of_mem _ hi₀ hi₀]
    simp [i₀, IsAnisotropic.rootForm_root_ne_zero]
  have hscale : InvariantForm.componentScale P.simplyLacedForm B C = 1 := by
    rw [← hcomp, InvariantForm.componentScale_eq_div, hB i₀, hslf, div_self two_ne_zero]
  ext x y
  simp [InvariantForm.form_apply_eq_componentScale_mul P.simplyLacedForm B x.2 y.2, hscale]

section SimplyLaced

variable [P.IsReduced]

/-- When `b.cartanMatrix` is simply laced, every root has squared length `2` under
`P.simplyLacedForm`. -/
theorem simplyLacedForm_root_self (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced) (i : ι) :
    P.simplyLacedForm.form (P.root i) (P.root i) = 2 := by
  let _ := Fintype.ofFinite ι
  rw [simplyLacedForm, InvariantForm.ofComponent_form_apply_of_mem _
    (root_mem_componentSpace i) (root_mem_componentSpace i)]
  have hcomp : P.componentOf (P.componentOf i).nonempty_supp.some = P.componentOf i :=
    ((P.componentOf i).mem_supp_iff _).mp (P.componentOf i).nonempty_supp.some_mem
  have heq : P.RootForm (P.root (P.componentOf i).nonempty_supp.some)
      (P.root (P.componentOf i).nonempty_supp.some) = P.RootForm (P.root i) (P.root i) :=
    P.toInvariantForm.apply_root_root_eq_of_componentOf_eq b hsimply hcomp
  simp [heq, IsAnisotropic.rootForm_root_ne_zero]

/-- Pairing against `P.root i` under `P.simplyLacedForm` coincides with the coroot functional
`P.coroot' i` when `b.cartanMatrix` is simply laced. -/
theorem simplyLacedForm_apply_root (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    (x : M) (i : ι) :
    P.simplyLacedForm.form x (P.root i) = P.coroot' i x := by
  have h := P.simplyLacedForm.two_mul_apply_root x i
  rw [P.simplyLacedForm_root_self b hsimply i, mul_comm (P.coroot' i x)] at h
  exact mul_left_cancel₀ two_ne_zero h

/-- Pairing `P.root i` against `x` under `P.simplyLacedForm` coincides with the coroot functional
`P.coroot' i x` when `b.cartanMatrix` is simply laced. -/
theorem simplyLacedForm_root_apply (b : P.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    (i : ι) (x : M) :
    P.simplyLacedForm.form (P.root i) x = P.coroot' i x := by
  have hsymm : P.simplyLacedForm.form (P.root i) x = P.simplyLacedForm.form x (P.root i) := by
    simpa using (P.simplyLacedForm.symm.eq x (P.root i)).symm
  rw [hsymm, P.simplyLacedForm_apply_root b hsimply]

end SimplyLaced

section Hom

variable {P}
variable {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {Q : RootPairing ι₂ K M₂ N₂} [Finite ι₂] [Q.IsRootSystem] [Q.IsCrystallographic] [Q.IsReduced]

/-- **Pulling back `simplyLacedForm` along a morphism into a simply laced root system gives
`simplyLacedForm`.** -/
theorem InvariantForm.comap_simplyLacedForm (b : Q.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    (f : P.Hom Q) :
    InvariantForm.comap f Q.simplyLacedForm = P.simplyLacedForm :=
  P.eq_simplyLacedForm_of_root_self fun i ↦ by
    rw [InvariantForm.comap_form_apply, f.root_weightMap_apply,
      Q.simplyLacedForm_root_self b hsimply]

/-- A morphism into a simply laced root system preserves `simplyLacedForm` on weights. -/
theorem Hom.simplyLacedForm_weightMap (b : Q.Base) (hsimply : b.cartanMatrix.IsSimplyLaced)
    (f : P.Hom Q) (x y : M) :
    Q.simplyLacedForm.form (f.weightMap x) (f.weightMap y) = P.simplyLacedForm.form x y := by
  simpa [InvariantForm.comap_form_apply] using
    congrArg (fun B : P.InvariantForm ↦ B.form x y)
      (InvariantForm.comap_simplyLacedForm (P := P) b hsimply f)

end Hom

end Field

end RootPairing
