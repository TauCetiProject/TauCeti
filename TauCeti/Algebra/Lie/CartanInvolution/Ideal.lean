/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.Semisimple.Basic
import TauCeti.Algebra.Lie.Killing.Prod

/-!
# Cartan involutions and the simple ideals

A Cartan involution `θ` of a real semisimple Lie algebra `𝔤₀` preserves every simple ideal: the
Killing form `B` vanishes between two ideals with trivial intersection, while `B(x, θ x) < 0` for
`x ≠ 0`, so a nonzero ideal meets its image under `θ`. Conversely, Cartan involutions of the
summands of an internal direct sum of ideals, in particular of the simple ideals, assemble into a
Cartan involution of `𝔤₀`. Finally `𝔤₀` is the direct sum of its *compact ideal*, the sum of the
simple ideals on which the Killing form is negative definite, and its *noncompact ideal*, the sum
of the other simple ideals; both are `θ`-stable, `θ` is the identity on the compact ideal, and the
`-1`-eigenspace `𝔭` of `θ` lies in the noncompact ideal.

Simple ideals are the atoms of the lattice of Lie ideals, as in Mathlib's
`LieAlgebra.IsSemisimple`.

## Main definitions

* `LieEquiv.ofIsInternal`: the automorphism of `L` acting by `θ i` on the summand `I i` of an
  internal direct sum of Lie ideals.
* `LieAlgebra.compactIdeal`, `LieAlgebra.noncompactIdeal`: the sum of the simple ideals on which
  the Killing form is, respectively is not, negative definite.

## Main results

* `LieIdeal.killingForm_eq_zero_of_disjoint`: the Killing form vanishes between Lie ideals with
  trivial intersection.
* `LieEquiv.IsCartanInvolution.map_eq_of_isAtom`: a Cartan involution preserves every simple
  ideal.
* `LieEquiv.isCartanInvolution_ofIsInternal`: Cartan involutions of the summands of an internal
  direct sum of ideals assemble into a Cartan involution.
* `LieAlgebra.IsSemisimple.isInternal_atoms`: a semisimple Lie algebra is the internal direct sum
  of its simple ideals, so `LieEquiv.ofIsInternal` applies to them.
* `LieAlgebra.forall_killingForm_neg_iff`: a simple ideal lies in the compact ideal exactly when
  it is a compact Lie algebra, that is, its own Killing form is negative definite.
* `LieAlgebra.isCompl_compactIdeal_noncompactIdeal`: a semisimple Lie algebra is the direct sum of
  its compact and noncompact ideals.
* `LieEquiv.IsCartanInvolution.map_compactIdeal`,
  `LieEquiv.IsCartanInvolution.map_noncompactIdeal`: both are stable under a Cartan involution.
* `LieEquiv.IsCartanInvolution.forall_apply_eq_iff_of_isAtom`: a simple ideal is compact exactly
  when a Cartan involution fixes it pointwise.
* `LieEquiv.IsCartanInvolution.cartanP_le_noncompactIdeal`: `𝔭` lies in the noncompact ideal.
* `LieEquiv.not_isCartanInvolution_prodComm`: the flip of `L × L` is not a Cartan involution for
  nontrivial `L`; for `L = 𝔰𝔩₂(ℝ)` its fixed algebra is the diagonal.

## References

* J.-H. Eschenburg, *Lecture Notes on Symmetric Spaces*, §7.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
-/

public section

open LieAlgebra LieModule

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The bracket of elements of two Lie ideals with trivial intersection vanishes. -/
theorem lie_eq_zero_of_disjoint {I J : LieIdeal R L} (h : Disjoint I J) {x y : L} (hx : x ∈ I)
    (hy : y ∈ J) : ⁅x, y⁆ = 0 :=
  (LieSubmodule.mem_bot _).mp <| h.le_bot <|
    (LieSubmodule.mem_inf _ _ _).mpr ⟨lie_mem_left R L I x y hx, lie_mem_right R L J x y hy⟩

/-- The Killing form vanishes between two Lie ideals with trivial intersection. -/
theorem killingForm_eq_zero_of_disjoint {I J : LieIdeal R L} (h : Disjoint I J) {x y : L}
    (hx : x ∈ I) (hy : y ∈ J) : killingForm R L x y = 0 := by
  have : toEnd R L L x ∘ₗ toEnd R L L y = 0 := by
    ext z
    exact lie_eq_zero_of_disjoint h hx (lie_mem_left R L J y z hy)
  rw [killingForm, traceForm_apply_apply, this, map_zero]

end LieIdeal

namespace LieEquiv

/-! ### Cartan involutions preserve the simple ideals -/

section Preserve

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L}

namespace IsCartanInvolution

/-- A nonzero Lie ideal meets its image under a Cartan involution. -/
theorem inf_map_ne_bot (hθ : θ.IsCartanInvolution) {I : LieIdeal K L} (hI : I ≠ ⊥) :
    I ⊓ I.map θ.toLieHom ≠ ⊥ := by
  intro h
  obtain ⟨x, hx, hx₀⟩ := (Submodule.ne_bot_iff I.toSubmodule).mp
    ((LieSubmodule.toSubmodule_eq_bot I).not.mpr hI)
  exact (hθ.killingForm_apply_apply_neg hx₀).ne
    (LieIdeal.killingForm_eq_zero_of_disjoint (disjoint_iff.mpr h) hx (LieIdeal.mem_map hx))

/-- A Cartan involution maps every simple ideal (an atom of the lattice of Lie ideals) into
itself. -/
theorem apply_mem_of_isAtom (hθ : θ.IsCartanInvolution) {I : LieIdeal K L} (hI : IsAtom I)
    {x : L} (hx : x ∈ I) : θ x ∈ I := by
  have hle : I ≤ I.map θ.toLieHom :=
    inf_eq_left.mp (((hI.le_iff).mp inf_le_left).resolve_left (hθ.inf_map_ne_bot hI.1))
  have := LieIdeal.mem_map_equiv.mp (hle hx)
  rwa [θ.symm_apply_eq.mpr (hθ.involutive x).symm] at this

/-- A Cartan involution maps every simple ideal (an atom of the lattice of Lie ideals) onto
itself. -/
theorem map_eq_of_isAtom (hθ : θ.IsCartanInvolution) {I : LieIdeal K L} (hI : IsAtom I) :
    I.map θ.toLieHom = I := by
  refine le_antisymm (LieIdeal.map_le_iff_le_comap.mpr fun x hx ↦ hθ.apply_mem_of_isAtom hI hx)
    fun x hx ↦ LieIdeal.mem_map_equiv.mpr ?_
  rw [θ.symm_apply_eq.mpr (hθ.involutive x).symm]
  exact hθ.apply_mem_of_isAtom hI hx

end IsCartanInvolution

end Preserve

/-! ### Assembling automorphisms of the summands of an internal direct sum -/

section OfIsInternal

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [DecidableEq ι]
  {I : ι → LieIdeal R L} (h : DirectSum.IsInternal fun i ↦ (I i).toSubmodule)
  (θ : ∀ i, I i ≃ₗ⁅R⁆ I i)

/-- The identification of the external direct sum of the summands of an internal direct sum with
`L`. -/
private noncomputable abbrev sumEquiv : (DirectSum ι fun i ↦ I i) ≃ₗ[R] L :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i ↦ (I i).toSubmodule) h

/-- The linear automorphism of `L` acting by `θ i` on each summand of an internal direct sum. -/
private noncomputable def linearOfIsInternal : L ≃ₗ[R] L :=
  (sumEquiv h).symm ≪≫ₗ
    DFinsupp.mapRange.linearEquiv (fun i ↦ (θ i).toLinearEquiv) ≪≫ₗ sumEquiv h

private theorem sumEquiv_apply (y : DirectSum ι fun i ↦ I i) :
    sumEquiv h y = DirectSum.coeLinearMap (fun i ↦ (I i).toSubmodule) y :=
  rfl

private theorem linearOfIsInternal_apply_of_mem {i : ι} {x : L} (hx : x ∈ I i) :
    linearOfIsInternal h θ x = θ i ⟨x, hx⟩ := by
  have hs : (sumEquiv h).symm x = DirectSum.of (fun i ↦ (I i).toSubmodule) i ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq, sumEquiv_apply, DirectSum.coeLinearMap_of]
  have hm : DFinsupp.mapRange.linearEquiv (fun i ↦ (θ i).toLinearEquiv)
      (DirectSum.of (fun i ↦ (I i).toSubmodule) i ⟨x, hx⟩) =
        DirectSum.of (fun i ↦ (I i).toSubmodule) i (θ i ⟨x, hx⟩) := by
    simp only [DFinsupp.mapRange.linearEquiv_apply, DirectSum.of]
    exact DFinsupp.mapRange_single
  rw [linearOfIsInternal, LinearEquiv.trans_apply, LinearEquiv.trans_apply, hs, hm,
    sumEquiv_apply, DirectSum.coeLinearMap_of]

private theorem linearOfIsInternal_mem {i : ι} {x : L} (hx : x ∈ I i) :
    linearOfIsInternal h θ x ∈ I i := by
  rw [linearOfIsInternal_apply_of_mem h θ hx]
  exact (θ i ⟨x, hx⟩).property

include h in
private theorem induction {P : L → Prop} (hP : ∀ i, ∀ x ∈ I i, P x) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (x : L) : P x :=
  Submodule.iSup_induction _ (motive := P) (h.submodule_iSup_eq_top ▸ Submodule.mem_top) hP h0
    hadd

include h in
private theorem disjoint {i j : ι} (hij : i ≠ j) : Disjoint (I i) (I j) :=
  (LieSubmodule.iSupIndep_toSubmodule.mp h.submodule_iSupIndep).pairwiseDisjoint hij

private theorem linearOfIsInternal_map_lie (x y : L) :
    linearOfIsInternal h θ ⁅x, y⁆ = ⁅linearOfIsInternal h θ x, linearOfIsInternal h θ y⁆ := by
  induction x using induction h with
  | h0 => simp
  | hadd x x' hx hx' => simp only [add_lie, map_add, hx, hx']
  | hP i x hx =>
    induction y using induction h with
    | h0 => simp
    | hadd y y' hy hy' => simp only [lie_add, map_add, hy, hy']
    | hP j y hy =>
      by_cases hij : i = j
      · subst hij
        rw [linearOfIsInternal_apply_of_mem h θ (lie_mem_left R L (I i) x y hx),
          linearOfIsInternal_apply_of_mem h θ hx, linearOfIsInternal_apply_of_mem h θ hy]
        exact congrArg Subtype.val ((θ i).map_lie ⟨x, hx⟩ ⟨y, hy⟩)
      · rw [LieIdeal.lie_eq_zero_of_disjoint (disjoint h hij) hx hy,
          LieIdeal.lie_eq_zero_of_disjoint (disjoint h hij) (linearOfIsInternal_mem h θ hx)
            (linearOfIsInternal_mem h θ hy), map_zero]

/-- The Lie algebra automorphism of `L` acting by `θ i` on the summand `I i` of an internal direct
sum of Lie ideals. -/
noncomputable def ofIsInternal : L ≃ₗ⁅R⁆ L :=
  { linearOfIsInternal h θ with
    map_lie' := fun {x y} ↦ linearOfIsInternal_map_lie h θ x y }

/-- `LieEquiv.ofIsInternal` acts by `θ i` on the summand `I i`. -/
theorem ofIsInternal_apply_of_mem {i : ι} {x : L} (hx : x ∈ I i) :
    ofIsInternal h θ x = θ i ⟨x, hx⟩ :=
  linearOfIsInternal_apply_of_mem h θ hx

/-- `LieEquiv.ofIsInternal` is the unique linear map acting by `θ i` on each summand `I i`. -/
theorem eq_ofIsInternal_iff (f : L →ₗ[R] L) :
    f = (ofIsInternal h θ : L →ₗ[R] L) ↔ ∀ i (x : I i), f x = θ i x := by
  refine ⟨fun hf i x ↦ by rw [hf]; exact ofIsInternal_apply_of_mem h θ x.property, fun hf ↦ ?_⟩
  refine LinearMap.ext fun x ↦ ?_
  induction x using induction h with
  | h0 => simp
  | hadd x x' hx hx' => simp only [map_add, hx, hx']
  | hP i x hx =>
    exact (hf i ⟨x, hx⟩).trans (ofIsInternal_apply_of_mem h θ hx).symm

end OfIsInternal

section IsCartanInvolutionOfIsInternal

variable {K L ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] [DecidableEq ι] {I : ι → LieIdeal K L}
  (h : DirectSum.IsInternal fun i ↦ (I i).toSubmodule) {θ : ∀ i, I i ≃ₗ⁅K⁆ I i}

/-- Cartan involutions of the summands of an internal direct sum of Lie ideals of a
finite-dimensional Lie algebra assemble into a Cartan involution. With
`LieAlgebra.IsSemisimple.isInternal_atoms` this applies to the simple ideals of a semisimple Lie
algebra. -/
theorem isCartanInvolution_ofIsInternal [FiniteDimensional K L]
    (hθ : ∀ i, (θ i).IsCartanInvolution) : (ofIsInternal h θ).IsCartanInvolution := by
  classical
  set f := ofIsInternal h θ
  have hf : ∀ i (x : I i), f x = θ i x := fun i x ↦ ofIsInternal_apply_of_mem h θ x.property
  refine isCartanInvolution_iff.mpr ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · have hff : (f.toLinearMap ∘ₗ f.toLinearMap) = (ofIsInternal h fun i ↦ (θ i).trans (θ i)) :=
      (eq_ofIsInternal_iff h _ _).mpr fun i x ↦ by simp [hf]
    have hid : (LinearMap.id : L →ₗ[K] L) = (ofIsInternal h fun i ↦ (θ i).trans (θ i)) :=
      (eq_ofIsInternal_iff h _ _).mpr fun i x ↦ by simp [(hθ i).involutive x]
    exact LinearMap.congr_fun (hff.trans hid.symm) x
  -- Write `x` as the sum of its components `d i ∈ I i`.
  set d := (sumEquiv h).symm x
  have hx' : x = ∑ i ∈ d.support, (d i : L) := by
    conv_lhs => rw [← (sumEquiv h).apply_symm_apply x]
    rw [sumEquiv_apply, DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum]
  have hkill : ∀ i (y : I i), killingForm K L y (θ i y) = killingForm K (I i) y (θ i y) :=
    fun i y ↦ (LinearMap.congr_fun₂ (LieIdeal.killingForm_eq (I := I i)) y (θ i y)).symm
  have hsum : killingForm K L x (f x) =
      ∑ i ∈ d.support, killingForm K (I i) (d i) (θ i (d i)) := by
    calc killingForm K L x (f x)
        = ∑ i ∈ d.support, ∑ j ∈ d.support, killingForm K L (d i) (f (d j)) := by
          conv_lhs => rw [hx']
          simp only [map_sum, LinearMap.sum_apply]
          exact Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i hi ↦ by
          rw [Finset.sum_eq_single i (fun j _ hji ↦ ?_) (fun h ↦ absurd hi h), hf, hkill]
          rw [hf]
          exact LieIdeal.killingForm_eq_zero_of_disjoint (disjoint h hji.symm) (d i).property
            (θ j (d j)).property
  rw [hsum]
  refine Finset.sum_neg (fun i hi ↦ (hθ i).killingForm_apply_apply_neg
    (DFinsupp.mem_support_iff.mp hi)) (Finset.nonempty_of_ne_empty fun hd0 ↦ ?_)
  exact hx (by rw [hx', hd0, Finset.sum_empty])

end IsCartanInvolutionOfIsInternal

/-! ### The flip of `L × L` -/

/-- The flip of `L × L` is not a Cartan involution for nontrivial `L`: it exchanges the ideals
`L × 0` and `0 × L` instead of preserving them. For `L = 𝔰𝔩₂(ℝ)` it is an involutive
automorphism whose fixed algebra is the diagonal `𝔰𝔩₂(ℝ)`. -/
theorem not_isCartanInvolution_prodComm {K L : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [LieRing L] [LieAlgebra K L] [Nontrivial L] :
    ¬ (LieEquiv.prodComm (R := K) (L₁ := L) (L₂ := L)).IsCartanInvolution := by
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have hd : Disjoint (LieHom.snd K L L).ker (LieHom.fst K L L).ker :=
    disjoint_iff.mpr <| eq_bot_iff.mpr fun p hp ↦ by
      obtain ⟨h2, h1⟩ := (LieSubmodule.mem_inf _ _ _).mp hp
      exact (LieSubmodule.mem_bot _).mpr (Prod.ext (by simpa using h1) (by simpa using h2))
  exact (hθ.killingForm_apply_apply_neg (x := (x, 0)) (by simp [hx])).ne
    (LieIdeal.killingForm_eq_zero_of_disjoint hd (by simp) (by simp))

end LieEquiv

/-! ### The compact and noncompact ideals -/

namespace LieAlgebra

section Atoms

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

open Classical in
/-- A semisimple Lie algebra is the internal direct sum of its simple ideals. -/
theorem IsSemisimple.isInternal_atoms [IsSemisimple R L] :
    DirectSum.IsInternal fun I : {I : LieIdeal R L // IsAtom I} ↦ (I : LieIdeal R L).toSubmodule :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr
      ((sSupIndep_iff _).mp IsSemisimple.sSupIndep_isAtom))
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr
      ((sSup_eq_iSup' _).symm.trans IsSemisimple.sSup_atoms_eq_top))

end Atoms

variable (K L : Type*) [Field K] [LinearOrder K] [LieRing L] [LieAlgebra K L]

/-- The *compact ideal* of a Lie algebra over an ordered field: the sum of the simple ideals on
which the Killing form is negative definite. -/
noncomputable def compactIdeal : LieIdeal K L :=
  sSup {I | IsAtom I ∧ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0}

/-- The *noncompact ideal* of a Lie algebra over an ordered field: the sum of the simple ideals on
which the Killing form is not negative definite. -/
noncomputable def noncompactIdeal : LieIdeal K L :=
  sSup {I | IsAtom I ∧ ¬ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0}

/-- The compact ideal is the sum of the simple ideals with negative definite Killing form. The
definition is not exposed, so this is how it is unfolded. -/
theorem compactIdeal_def : compactIdeal K L =
    sSup {I | IsAtom I ∧ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0} :=
  (rfl)

/-- The noncompact ideal is the sum of the other simple ideals. The definition is not exposed, so
this is how it is unfolded. -/
theorem noncompactIdeal_def : noncompactIdeal K L =
    sSup {I | IsAtom I ∧ ¬ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0} :=
  (rfl)

variable {K L}

/-- On a Lie ideal of a finite-dimensional Lie algebra, the Killing form of `L` is negative
definite exactly when the Killing form of the ideal is: a simple ideal is in the compact ideal
exactly when it is a compact Lie algebra. -/
theorem forall_killingForm_neg_iff [FiniteDimensional K L] (I : LieIdeal K L) :
    (∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0) ↔
      ∀ x : I, x ≠ 0 → killingForm K I x x < 0 := by
  have hkill : ∀ x : I, killingForm K I x x = killingForm K L x x := fun x ↦
    LinearMap.congr_fun₂ (LieIdeal.killingForm_eq (I := I)) x x
  simp only [hkill]
  exact ⟨fun h x hx ↦ h x x.property (by simpa using hx),
    fun h x hx hx₀ ↦ h ⟨x, hx⟩ (by simpa using hx₀)⟩

/-- A semisimple Lie algebra over an ordered field is the direct sum of its compact ideal and its
noncompact ideal. -/
theorem isCompl_compactIdeal_noncompactIdeal [IsSemisimple K L] :
    IsCompl (compactIdeal K L) (noncompactIdeal K L) := by
  have hind := (IsSemisimple.sSupIndep_isAtom (R := K) (L := L))
  refine ⟨?_, codisjoint_iff.mpr ?_⟩
  · have himage : ∀ Q : LieIdeal K L → Prop, sSup {I | IsAtom I ∧ Q I} =
        ⨆ J ∈ {J : {I : LieIdeal K L | IsAtom I} | Q J}, (J : LieIdeal K L) := fun Q ↦ by
      rw [← sSup_image]
      congr 1
      ext I
      simp [and_comm]
    rw [compactIdeal_def, noncompactIdeal_def, himage, himage]
    exact ((sSupIndep_iff _).mp hind).disjoint_biSup_biSup
      (Set.disjoint_left.mpr fun _ h₁ h₂ ↦ h₂ h₁)
  · rw [compactIdeal_def, noncompactIdeal_def, ← sSup_union, ← IsSemisimple.sSup_atoms_eq_top]
    congr 1
    ext I
    simp only [Set.mem_union, Set.mem_ofPred_eq, ← and_or_left, or_not, and_true]

end LieAlgebra

namespace LieEquiv.IsCartanInvolution

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L}

private theorem map_sSup_of_forall_isAtom (hθ : θ.IsCartanInvolution) {S : Set (LieIdeal K L)}
    (hS : ∀ I ∈ S, IsAtom I) : (sSup S).map θ.toLieHom = sSup S := by
  rw [(LieIdeal.gc_map_comap θ.toLieHom).l_sSup, sSup_eq_iSup]
  exact iSup_congr fun I ↦ iSup_congr fun hI ↦ hθ.map_eq_of_isAtom (hS I hI)

/-- The compact ideal is stable under a Cartan involution. -/
theorem map_compactIdeal (hθ : θ.IsCartanInvolution) :
    (compactIdeal K L).map θ.toLieHom = compactIdeal K L :=
  hθ.map_sSup_of_forall_isAtom fun _ hI ↦ hI.1

/-- The noncompact ideal is stable under a Cartan involution. -/
theorem map_noncompactIdeal (hθ : θ.IsCartanInvolution) :
    (noncompactIdeal K L).map θ.toLieHom = noncompactIdeal K L :=
  hθ.map_sSup_of_forall_isAtom fun _ hI ↦ hI.1

/-- A simple ideal has negative definite Killing form exactly when a Cartan involution fixes it
pointwise. -/
theorem forall_apply_eq_iff_of_isAtom (hθ : θ.IsCartanInvolution) {I : LieIdeal K L}
    (hI : IsAtom I) :
    (∀ x ∈ I, θ x = x) ↔ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0 := by
  refine ⟨fun h x hx hx₀ ↦ ?_, fun h x hx ↦ ?_⟩
  · simpa [h x hx] using hθ.killingForm_apply_apply_neg hx₀
  · -- `x - θ x` lies in `I ∩ 𝔭`, where the Killing form is both negative and positive definite.
    have hp : x - θ x ∈ θ.cartanP := mem_cartanP.mpr (by rw [map_sub, hθ.involutive x, neg_sub])
    have hpI : x - θ x ∈ I := sub_mem hx (hθ.apply_mem_of_isAtom hI hx)
    by_contra hne
    have hne' : x - θ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    exact (h _ hpI hne').asymm (hθ.killingForm_apply_self_pos_of_mem_cartanP hp hne')

/-- A Cartan involution is the identity on the compact ideal. -/
theorem apply_eq_of_mem_compactIdeal (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ compactIdeal K L) : θ x = x := by
  have hle : (compactIdeal K L).toSubmodule ≤ θ.toLieHom.fixedSubalgebra.toSubmodule := by
    rw [compactIdeal_def, LieSubmodule.sSup_toSubmodule, sSup_le_iff]
    rintro _ ⟨I, ⟨hI, hIP⟩, rfl⟩ x hx
    exact (LieSubalgebra.mem_toSubmodule _).mpr <| LieHom.mem_fixedSubalgebra.mpr <|
      (hθ.forall_apply_eq_iff_of_isAtom hI).mpr hIP x hx
  exact LieHom.mem_fixedSubalgebra.mp ((LieSubalgebra.mem_toSubmodule _).mp (hle hx))

/-- The `-1`-eigenspace `𝔭` of a Cartan involution lies in the noncompact ideal. -/
theorem cartanP_le_noncompactIdeal (hθ : θ.IsCartanInvolution) :
    θ.cartanP ≤ (noncompactIdeal K L).toSubmodule := by
  have := hθ.isSemisimple
  intro x hx
  have hc := LieAlgebra.isCompl_compactIdeal_noncompactIdeal (K := K) (L := L)
  have htop : (compactIdeal K L).toSubmodule ⊔ (noncompactIdeal K L).toSubmodule = ⊤ := by
    rw [← LieSubmodule.sup_toSubmodule, hc.sup_eq_top, LieSubmodule.top_toSubmodule]
  obtain ⟨c, hcm, n, hn, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : x ∈ _)
  have hθn : θ n ∈ noncompactIdeal K L := by
    rw [← hθ.map_noncompactIdeal]
    exact LieIdeal.mem_map hn
  -- `θ (c + n) = -(c + n)` and `θ c = c` give `2 c = -(n + θ n)`, in both ideals.
  have h2 : (2 : K) • c = -(n + θ n) := by
    have := mem_cartanP.mp hx
    rw [map_add, hθ.apply_eq_of_mem_compactIdeal hcm] at this
    linear_combination (norm := module) this
  have h2c : (2 : K) • c = 0 :=
    (LieSubmodule.mem_bot _).mp <| hc.disjoint.le_bot <| (LieSubmodule.mem_inf _ _ _).mpr
      ⟨SMulMemClass.smul_mem _ hcm, h2 ▸ neg_mem (add_mem hn hθn)⟩
  obtain rfl : c = 0 := (smul_eq_zero.mp h2c).resolve_left two_ne_zero
  simpa using hn

end LieEquiv.IsCartanInvolution
