/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Component.Basic
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.Component.Base
import TauCeti.LinearAlgebra.RootSystem.Component.InvariantForm
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Invariant forms on simply laced root systems

In a simply laced root pairing all roots in the same irreducible component have the same squared
length for every invariant form; when the pairing is irreducible, all roots have the same length
and two roots whose sum is again a root have Cartan integer `-1`.

Over a linearly ordered field, rescaling the canonical root form on each irreducible component
produces the unique invariant form of a simply laced finite reduced crystallographic root system on
which every root has squared length `2` (`RootPairing.Base.simplyLacedInvariantForm`). This form is
positive definite, evaluates on `(x, αⱼ)` to the coroot pairing `⟨x, αⱼ^∨⟩` (and on `(αᵢ, αⱼ)` to
`P.pairing i j`), and by uniqueness is invariant under every root-system automorphism.

## Main definitions

* `RootPairing.Base.simplyLacedInvariantForm`: the unique invariant form of a simply laced root
  system over a linearly ordered field giving every root squared length `2`.

## Main results

* `RootPairing.InvariantForm.eq_of_forall_apply_root_self_eq`: an invariant form of a root system
  is determined by the squared lengths of the roots.
* `RootPairing.InvariantForm.apply_root_root_eq_of_componentOf_eq`: in a simply laced root pairing
  all roots in the same irreducible component have the same length.
* `RootPairing.InvariantForm.apply_root_root_eq_of_isSimplyLaced`: in a simply laced irreducible
  root system all roots have the same length.
* `RootPairing.Base.pairingIn_eq_neg_one_of_isSimplyLaced`: two roots whose sum is a root have
  Cartan integer `-1`.
* `RootPairing.Base.posDef_simplyLacedInvariantForm`,
  `RootPairing.Base.simplyLacedInvariantForm_root_self`,
  `RootPairing.Base.simplyLacedInvariantForm_root_root`,
  `RootPairing.Base.simplyLacedInvariantForm_apply_root`,
  `RootPairing.Base.comap_simplyLacedInvariantForm`: positivity, normalization, pairing formulas,
  and full automorphism invariance of `RootPairing.Base.simplyLacedInvariantForm`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, no. 4.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **An invariant form of a root system is determined by the squared lengths of the roots.** -/
theorem InvariantForm.eq_of_forall_apply_root_self_eq [CharZero R] [IsDomain R] [P.IsRootSystem]
    {B₁ B₂ : P.InvariantForm}
    (h : ∀ i : ι, B₁.form (P.root i) (P.root i) = B₂.form (P.root i) (P.root i)) : B₁ = B₂ := by
  ext : 1
  refine LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P)) fun i ↦
    LinearMap.ext_on_range (IsRootSystem.span_root_eq_top (P := P)) fun j ↦ ?_
  have h1 := B₁.two_mul_apply_root_root i j
  have h2 := B₂.two_mul_apply_root_root i j
  have htwo : (2 : R) ≠ 0 := two_ne_zero
  exact mul_left_cancel₀ htwo (by rw [h1, h2, h j])

/-- **In a simply laced root pairing all roots in the same irreducible component have the same
length** for every invariant form. -/
theorem InvariantForm.apply_root_root_eq_of_componentOf_eq [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) {i j : ι} (hij : P.componentOf i = P.componentOf j) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  have hadj {u v : b.support} (h : (TauCeti.diagramGraph b.cartanMatrix).Adj u v) :
      B.form (P.root u) (P.root u) = B.form (P.root v) (P.root v) := by
    have hne : u ≠ v := h.ne
    have hvu_nz : b.cartanMatrix v u ≠ 0 := (TauCeti.diagramGraph_adj.mp h).2.2
    have huv_nz : b.cartanMatrix u v ≠ 0 := (TauCeti.diagramGraph_adj.mp h).2.1
    have hvu : b.cartanMatrix v u = -1 := (hsl hne.symm).resolve_left hvu_nz
    have huv : b.cartanMatrix u v = -1 := (hsl hne).resolve_left huv_nz
    have hp (x y : b.support) (hxy : b.cartanMatrix x y = -1) : P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hxy
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    have hswap := B.pairing_mul_eq_pairing_mul_swap (u : ι) v
    rw [hp v u hvu, hp u v huv] at hswap
    linear_combination -hswap
  have hsimple {u v : b.support} (h : P.componentOf u = P.componentOf v) :
      B.form (P.root u) (P.root u) = B.form (P.root v) (P.root v) := by
    obtain ⟨w⟩ := b.reachable_nonorthogonalGraph_iff.mp (SimpleGraph.ConnectedComponent.exact h)
    clear h
    induction w with
    | nil => rfl
    | cons hadj' _ ih => exact (hadj hadj').trans ih
  have hrep (k : ι) : ∃ s ∈ b.support,
      P.componentOf s = P.componentOf k ∧
        B.form (P.root s) (P.root s) = B.form (P.root k) (P.root k) := by
    refine b.induction_reflect k
      (p := fun k ↦ ∃ s ∈ b.support, P.componentOf s = P.componentOf k ∧
        B.form (P.root s) (P.root s) = B.form (P.root k) (P.root k))
      ?_ (fun s hs ↦ ⟨s, hs, rfl, rfl⟩) ?_
    · rintro k ⟨s, hs, hc, hl⟩
      refine ⟨s, hs, hc.trans (componentOf_reflectionPerm k k).symm, ?_⟩
      rw [hl, root_reflectionPerm, B.apply_reflection_reflection]
    · rintro k r ⟨s, hs, hc, hl⟩ _
      refine ⟨s, hs, hc.trans (componentOf_reflectionPerm r k).symm, ?_⟩
      rw [hl, root_reflectionPerm, B.apply_reflection_reflection]
  obtain ⟨si, hsi, hci, hli⟩ := hrep i
  obtain ⟨sj, hsj, hcj, hlj⟩ := hrep j
  rw [← hli, ← hlj]
  exact hsimple (u := ⟨si, hsi⟩) (v := ⟨sj, hsj⟩) (hci.trans (hij.trans hcj.symm))

/-- **In a simply laced irreducible root system all roots have the same length** for every invariant
form. Irreducibility is needed: a system of type `A₁ × A₁` has invariant forms giving its two
components different lengths. -/
theorem InvariantForm.apply_root_root_eq_of_isSimplyLaced [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  have hsimple (l m : b.support) : B.form (P.root l) (P.root l) = B.form (P.root m) (P.root m) := by
    refine b.induction_on_cartanMatrix
      (fun k : b.support ↦ B.form (P.root l) (P.root l) = B.form (P.root k) (P.root k)) rfl ?_
    intro u v (huv : B.form (P.root l) (P.root l) = _) hne
    rcases eq_or_ne u v with rfl | hne'
    · exact huv
    have hvu : b.cartanMatrix v u = -1 := (hsl hne'.symm).resolve_left hne
    have huv' : b.cartanMatrix u v = -1 :=
      (hsl hne').resolve_left (b.cartanMatrix_apply_eq_zero_iff_symm.not.mp hne)
    have hp (x y : b.support) (hxy : b.cartanMatrix x y = -1) : P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hxy
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    have := B.pairing_mul_eq_pairing_mul_swap (u : ι) v
    rw [hp v u hvu, hp u v huv'] at this
    rw [huv]
    linear_combination -this
  have : Nonempty ι := ⟨i⟩
  obtain ⟨l⟩ : Nonempty b.support := b.support_nonempty.to_subtype
  have hall (x : ι) : B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l) := by
    refine b.induction_simple_reflect x
      (p := fun x ↦ B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l))
      (fun k hk ↦ hsimple ⟨k, hk⟩ l) fun k r hk _ ↦ ?_
    rw [← hk, root_reflectionPerm, B.apply_reflection_reflection]
  rw [hall i, hall j]

namespace Base

variable [CharZero R] (b : P.Base) [P.IsCrystallographic] [Finite ι] [IsDomain R] [P.IsReduced]

/-- **In a simply laced irreducible root system, two roots whose sum is a root have Cartan integer
`-1`.** -/
theorem pairingIn_eq_neg_one_of_isSimplyLaced [P.IsIrreducible]
    (hsl : b.cartanMatrix.IsSimplyLaced) {i k m : ι}
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

section Normalized

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Module K M] [Module K N] {P : RootPairing ι K M N} [Finite ι] [P.IsRootSystem]
  [P.IsCrystallographic]

/-- **The canonical norm-2 invariant form of a simply laced root system**: the unique positive-
definite invariant form obtained by rescaling the canonical root form on each irreducible component
so that every root has squared length `2`. Taking `hsl` ensures the component-wise scaling is
independent of the chosen representative root in each component. -/
noncomputable def Base.simplyLacedInvariantForm (b : P.Base)
    (_hsl : b.cartanMatrix.IsSimplyLaced) : P.InvariantForm :=
  letI := Fintype.ofFinite ι
  ((InvariantForm.posDefEquivScale P.toInvariantForm P.rootForm_posDef).symm fun C ↦
    ⟨2 / P.toInvariantForm.form (P.root C.nonempty_supp.some) (P.root C.nonempty_supp.some),
      div_pos zero_lt_two (P.rootForm_posDef _ (P.ne_zero _))⟩).1

/-- The canonical norm-2 invariant form of a simply laced root system is positive definite. -/
theorem Base.posDef_simplyLacedInvariantForm (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced) :
    (b.simplyLacedInvariantForm hsl).form.toQuadraticMap.PosDef := by
  let _ := Fintype.ofFinite ι
  exact ((InvariantForm.posDefEquivScale P.toInvariantForm P.rootForm_posDef).symm _).2

variable [P.IsReduced]

/-- Every root has squared length `2` for the canonical norm-2 invariant form. -/
theorem Base.simplyLacedInvariantForm_root_self (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced)
    (i : ι) :
    (b.simplyLacedInvariantForm hsl).form (P.root i) (P.root i) = 2 := by
  let _ := Fintype.ofFinite ι
  have hmem := P.root_mem_componentSpace i
  have hval := InvariantForm.form_posDefEquivScale_symm_apply_of_mem P.toInvariantForm
    P.rootForm_posDef (fun C ↦
      ⟨2 / P.toInvariantForm.form (P.root C.nonempty_supp.some) (P.root C.nonempty_supp.some),
        div_pos zero_lt_two (P.rootForm_posDef _ (P.ne_zero _))⟩) hmem hmem
  have hcomp : P.componentOf (P.componentOf i).nonempty_supp.some = P.componentOf i :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (P.componentOf i).nonempty_supp.some_mem
  have heq : P.RootForm (P.root (P.componentOf i).nonempty_supp.some)
      (P.root (P.componentOf i).nonempty_supp.some) = P.RootForm (P.root i) (P.root i) :=
    P.toInvariantForm.apply_root_root_eq_of_componentOf_eq b hsl hcomp
  have hne : P.RootForm (P.root i) (P.root i) ≠ 0 := P.toInvariantForm.ne_zero i
  rw [Base.simplyLacedInvariantForm]
  simpa [heq, div_mul_cancel₀ _ hne] using hval

/-- On any pair of roots, the canonical norm-2 invariant form equals the root-coroot pairing. -/
theorem Base.simplyLacedInvariantForm_root_root (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced)
    (i j : ι) :
    (b.simplyLacedInvariantForm hsl).form (P.root i) (P.root j) = P.pairing i j := by
  have h := (b.simplyLacedInvariantForm hsl).two_mul_apply_root_root i j
  rw [b.simplyLacedInvariantForm_root_self hsl j] at h
  exact mul_left_cancel₀ (two_ne_zero (α := K)) (by linear_combination h)

/-- Evaluating the canonical norm-2 invariant form against a root gives its coroot functional. -/
@[simp]
theorem Base.simplyLacedInvariantForm_apply_root (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced)
    (x : M) (j : ι) :
    (b.simplyLacedInvariantForm hsl).form x (P.root j) = P.coroot' j x := by
  have h := (b.simplyLacedInvariantForm hsl).two_mul_apply_root x j
  rw [b.simplyLacedInvariantForm_root_self hsl j] at h
  exact mul_left_cancel₀ (two_ne_zero (α := K)) (by linear_combination h)

/-- The canonical norm-2 invariant form is preserved by every automorphism of the root system. -/
@[simp]
theorem Base.comap_simplyLacedInvariantForm (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced)
    (σ : P.Aut) :
    InvariantForm.comap σ.toHom (b.simplyLacedInvariantForm hsl) =
      b.simplyLacedInvariantForm hsl := by
  refine InvariantForm.eq_of_forall_apply_root_self_eq fun i ↦ ?_
  rw [InvariantForm.comap_form_apply, Hom.root_weightMap_apply,
    b.simplyLacedInvariantForm_root_self hsl, b.simplyLacedInvariantForm_root_self hsl]

/-- Every automorphism of a simply laced root system is an isometry for the canonical norm-2
invariant form. -/
@[simp]
theorem Base.simplyLacedInvariantForm_weightMap (b : P.Base) (hsl : b.cartanMatrix.IsSimplyLaced)
    (σ : P.Aut) (x y : M) :
    (b.simplyLacedInvariantForm hsl).form (σ.weightMap x) (σ.weightMap y) =
      (b.simplyLacedInvariantForm hsl).form x y := by
  rw [← InvariantForm.comap_form_apply, b.comap_simplyLacedInvariantForm hsl σ]

end Normalized

end RootPairing
