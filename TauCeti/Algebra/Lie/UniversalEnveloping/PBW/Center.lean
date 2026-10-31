/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization

/-!
# The PBW symbols of central elements

Restrict the PBW filtration of `U(L)` to its centre `Z(U(L))`: the `n`-th step
`TauCeti.UniversalEnvelopingAlgebra.centerPBWFiltration R L n` consists of the central elements
of PBW degree at most `n`, and `TauCeti.UniversalEnvelopingAlgebra.CenterPBWGradedPiece R L n` is
the quotient by the central elements of degree below `n`. Taking PBW symbols embeds this quotient
in the graded piece `gr_n U(L)` (`TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedToPBWGraded`).

This file identifies the image. For `L` free over `R` and `n!` a unit in `R`, the PBW
theorem reads `gr_n U(L)` as the homogeneous component `S^n(L)`, and the symbols of the central
elements of degree `n` are exactly the homogeneous Lie invariants `S^n(L)^L`. This gives the
linear isomorphism

`Z_n / Z_{n-1} ≃ S^n(L)^L`

(`TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedInvariantIso`), compatible with the PBW
symbol and inverted by symmetrization. This is the graded comparison between `Z(U(L))` and
`S(L)^L` that, combined with Chevalley's restriction theorem, drives the degree induction in the
proof of the Harish-Chandra isomorphism.

The two inclusions are proved as follows.

* An invariant `p ∈ S^n(L)^L` is the symbol of its symmetrization, which is central
  (`TauCeti.UniversalEnvelopingAlgebra.pbwHomogeneousSymmetrization_mem_center`).
* Conversely let `z` be central of degree `n` with symbol `p ∈ S^n(L)`, so that `z` and the
  symmetrization `sym p` differ by an element of lower degree. Symmetrization intertwines the
  adjoint actions, so for `x ∈ L` the symmetrization of `x • p` is
  `⁅ι x, sym p⁆ = ⁅ι x, sym p - z⁆`, and bracketing with `ι x` does not raise the degree. Hence
  `sym (x • p)` has degree below `n`, its symbol `x • p` vanishes, and `p` is invariant
  (`TauCeti.UniversalEnvelopingAlgebra.mem_lieInvariants_of_pbwHomogeneousComponentMap_eq_mk`).

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.centerPBWFiltration` and
  `TauCeti.UniversalEnvelopingAlgebra.centerPBWFiltrationPrevious`: the PBW filtration restricted
  to the centre, and its preceding step.
* `TauCeti.UniversalEnvelopingAlgebra.CenterPBWGradedPiece`: the successive quotients of the
  restricted filtration.
* `TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedToPBWGraded`: the PBW symbol of the centre.
* `TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedInvariantIso`: the isomorphism with the
  homogeneous Lie invariants `S^n(L)^L`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedToPBWGraded_injective`: the PBW symbol of
  the centre is injective.
* `TauCeti.UniversalEnvelopingAlgebra.mem_lieInvariants_of_pbwHomogeneousComponentMap_eq_mk`:
  the symbol of a central element is a Lie invariant.
* `TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedInvariantIso_symbol` and
  `TauCeti.UniversalEnvelopingAlgebra.centerPBWGradedInvariantIso_symm_apply`: the isomorphism is
  the PBW symbol, and its inverse is symmetrization.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §23.3.
* J. Dixmier, *Enveloping Algebras*, §2.4.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.Algebra TauCeti.Algebra.wordFiltration TauCeti.SymmetricAlgebra

universe v

variable (R : Type) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)

/-! ### The PBW filtration of the centre -/

/-- The PBW filtration of the centre of `U(L)`: its `n`-th step consists of the central elements
of PBW degree at most `n`. -/
def centerPBWFiltration (n : ℕ) : Submodule R (Subalgebra.center R U) :=
  (pbwFiltration R L n).comap (Subalgebra.center R U).val.toLinearMap

/-- The step preceding degree `n` in the PBW filtration of the centre: the central elements of PBW
degree strictly below `n`. -/
def centerPBWFiltrationPrevious (n : ℕ) : Submodule R (Subalgebra.center R U) :=
  (pbwFiltrationPrevious R L n).comap (Subalgebra.center R U).val.toLinearMap

variable {R L} in
/-- A central element lies in the `n`-th step of the centre exactly when it has PBW degree at most
`n` in `U(L)`. -/
@[simp]
theorem mem_centerPBWFiltration {n : ℕ} {z : Subalgebra.center R U} :
    z ∈ centerPBWFiltration R L n ↔ (z : U) ∈ pbwFiltration R L n :=
  Iff.rfl

variable {R L} in
/-- A central element lies in the step of the centre preceding degree `n` exactly when it has PBW
degree below `n` in `U(L)`. -/
@[simp]
theorem mem_centerPBWFiltrationPrevious {n : ℕ} {z : Subalgebra.center R U} :
    z ∈ centerPBWFiltrationPrevious R L n ↔ (z : U) ∈ pbwFiltrationPrevious R L n :=
  Iff.rfl

/-- The step of the centre preceding degree zero is trivial. -/
@[simp]
theorem centerPBWFiltrationPrevious_zero : centerPBWFiltrationPrevious R L 0 = ⊥ := by
  ext z
  simp

/-- In successor degree, the preceding step of the centre is the previous filtration step. -/
@[simp]
theorem centerPBWFiltrationPrevious_succ (n : ℕ) :
    centerPBWFiltrationPrevious R L (n + 1) = centerPBWFiltration R L n := by
  ext z
  simp

/-- The degree-`n` successive quotient of the PBW filtration of the centre of `U(L)`. -/
abbrev CenterPBWGradedPiece (n : ℕ) : Type v :=
  centerPBWFiltration R L n ⧸
    (centerPBWFiltrationPrevious R L n).submoduleOf (centerPBWFiltration R L n)

/-- **The PBW symbol of the centre**: the class of a central element of degree at most `n` in the
degree-`n` graded piece of `U(L)`. -/
noncomputable def centerPBWGradedToPBWGraded (n : ℕ) :
    CenterPBWGradedPiece R L n →ₗ[R] PBWGradedPiece R L n :=
  Submodule.mapQ _ _
    ((Subalgebra.center R U).val.toLinearMap.restrict
      (p := centerPBWFiltration R L n) (q := wordFiltration (ι).toLinearMap n)
      fun _ hz ↦ by
        rw [AlgHom.toLinearMap_apply, Subalgebra.coe_val, ← pbwFiltration_def]
        exact mem_centerPBWFiltration.mp hz)
    fun z hz ↦ by
      simpa only [Submodule.mem_comap, mem_previousRestricted_iff, pbwFiltrationPrevious_def,
        LinearMap.restrict_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
        Submodule.coe_subtype] using
        mem_centerPBWFiltrationPrevious.mp hz

/-- The PBW symbol of the class of a central element is the class of that element. -/
@[simp]
theorem centerPBWGradedToPBWGraded_mk {n : ℕ} (z : centerPBWFiltration R L n) :
    centerPBWGradedToPBWGraded R L n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨((z : Subalgebra.center R U) : U),
        by simpa only [pbwFiltration_def] using mem_centerPBWFiltration.mp z.2⟩ :=
  (rfl)

/-- **The PBW symbol of the centre is injective**: a central element of degree at most `n` whose
degree-`n` symbol vanishes has degree below `n`. -/
theorem centerPBWGradedToPBWGraded_injective (n : ℕ) :
    Function.Injective (centerPBWGradedToPBWGraded R L n) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | _ z =>
      rw [centerPBWGradedToPBWGraded_mk, gradedPiece_mk_eq_zero_iff,
        ← pbwFiltrationPrevious_def] at hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx

/-! ### The symbols of central elements are Lie invariants -/

variable {R L}

/-- **The PBW symbol of a central element is a Lie invariant.** If `z` is central of PBW degree at
most `n` and the homogeneous polynomial `p ∈ S^n(L)` has the degree-`n` class of `z` as its PBW
image, then `p` is killed by the adjoint action of `L`. This needs `L` free, so that `S^n(L)` embeds
in `gr_n U(L)`, and `n!` a unit, to symmetrize. -/
theorem mem_lieInvariants_of_pbwHomogeneousComponentMap_eq_mk [Module.Free R L] {n : ℕ}
    (hn : IsUnit (n.factorial : R)) {z : U} (hz : z ∈ Subalgebra.center R U)
    (hzn : z ∈ wordFiltration (ι).toLinearMap n) {p : homogeneousSubmodule R L n}
    (hp : pbwHomogeneousComponentMap R L n p = Submodule.Quotient.mk ⟨z, hzn⟩) :
    (p : SymmetricAlgebra R L) ∈ lieInvariants R L L := by
  refine mem_lieInvariants.mpr fun x ↦ ?_
  let s := pbwHomogeneousSymmetrization R L n hn
  -- The symmetrization of `p` has the same symbol as `z`, so they differ in lower degree.
  have hsz : s p - z ∈ pbwFiltrationPrevious R L n := by
    have h := (mk_pbwHomogeneousSymmetrization R L n hn p).trans hp
    rwa [Submodule.Quotient.eq, mem_previousRestricted_iff, ← pbwFiltrationPrevious_def] at h
  let q : homogeneousSubmodule R L n :=
    ⟨lieModuleDerivation R L L x p, lieModuleDerivation_mem_homogeneousSubmodule R L L x p.2⟩
  -- The symmetrization of `x • p` is `⁅ι x, s p - z⁆`, again of lower degree.
  have hq : s q ∈ pbwFiltrationPrevious R L n := by
    have hzx : ⁅ι x, z⁆ = 0 := by
      rw [← lie_skew, (mem_center_iff_forall_lie_ι R L).mp hz x, neg_zero]
    rw [← lie_ι_pbwHomogeneousSymmetrization R L n hn x (p := p) rfl, ← sub_zero ⁅ι x, s p⁆,
      ← hzx, ← lie_sub]
    exact lie_ι_mem_pbwFiltrationPrevious R L x hsz
  -- So the symbol `x • p` of that symmetrization vanishes.
  have hq0 : q = 0 := pbwHomogeneousComponentMap_injective R L n <| by
    rw [← mk_pbwHomogeneousSymmetrization R L n hn, map_zero, gradedPiece_mk_eq_zero_iff,
      ← pbwFiltrationPrevious_def]
    exact hq
  exact congrArg Subtype.val hq0

/-! ### The centre symbols are the homogeneous invariants -/

/-- The homogeneous Lie invariants of degree `n`, mapped to `gr_n U(L)` by the PBW component. -/
private noncomputable def invariantToPBWGraded (n : ℕ) :
    (Subalgebra.toSubmodule (lieInvariants R L L) ⊓ homogeneousSubmodule R L n :
      Submodule R (SymmetricAlgebra R L)) →ₗ[R] PBWGradedPiece R L n :=
  (pbwHomogeneousComponentMap R L n).comp (Submodule.inclusion inf_le_right)

private theorem invariantToPBWGraded_apply {n : ℕ}
    (p : (Subalgebra.toSubmodule (lieInvariants R L L) ⊓ homogeneousSubmodule R L n :
      Submodule R (SymmetricAlgebra R L))) :
    invariantToPBWGraded n p =
      pbwHomogeneousComponentMap R L n ⟨p, (Submodule.mem_inf.mp p.2).2⟩ :=
  (rfl)

private theorem invariantToPBWGraded_injective [Module.Free R L] (n : ℕ) :
    Function.Injective (invariantToPBWGraded (R := R) (L := L) n) :=
  (pbwHomogeneousComponentMap_injective R L n).comp (Submodule.inclusion_injective _)

/-- The symmetrization of a homogeneous invariant, as a central element of degree at most `n`. -/
private noncomputable def symmetrizationCenter {n : ℕ} (hn : IsUnit (n.factorial : R))
    (p : (Subalgebra.toSubmodule (lieInvariants R L L) ⊓ homogeneousSubmodule R L n :
      Submodule R (SymmetricAlgebra R L))) :
    centerPBWFiltration R L n :=
  ⟨⟨pbwHomogeneousSymmetrization R L n hn ⟨p, (Submodule.mem_inf.mp p.2).2⟩,
      pbwHomogeneousSymmetrization_mem_center R L n hn (Submodule.mem_inf.mp p.2).1⟩,
    mem_centerPBWFiltration.mpr (pbwHomogeneousSymmetrization_mem_pbwFiltration R L n hn _)⟩

private theorem centerPBWGradedToPBWGraded_symmetrizationCenter {n : ℕ}
    (hn : IsUnit (n.factorial : R))
    (p : (Subalgebra.toSubmodule (lieInvariants R L L) ⊓ homogeneousSubmodule R L n :
      Submodule R (SymmetricAlgebra R L))) :
    centerPBWGradedToPBWGraded R L n (Submodule.Quotient.mk (symmetrizationCenter hn p)) =
      invariantToPBWGraded n p := by
  rw [centerPBWGradedToPBWGraded_mk, invariantToPBWGraded_apply]
  exact mk_pbwHomogeneousSymmetrization R L n hn _

private theorem range_centerPBWGradedToPBWGraded [Module.Free R L] {n : ℕ}
    (hn : IsUnit (n.factorial : R)) :
    LinearMap.range (centerPBWGradedToPBWGraded R L n) =
      LinearMap.range (invariantToPBWGraded (R := R) (L := L) n) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
        obtain ⟨p, hp⟩ := pbwHomogeneousComponentMap_surjective R L n
          (Submodule.Quotient.mk ⟨((z : Subalgebra.center R U) : U),
            by simpa only [pbwFiltration_def] using mem_centerPBWFiltration.mp z.2⟩)
        have hinv := mem_lieInvariants_of_pbwHomogeneousComponentMap_eq_mk hn
          (z : Subalgebra.center R U).2 _ hp
        exact ⟨⟨p, Submodule.mem_inf.mpr ⟨hinv, p.2⟩⟩,
          hp.trans (centerPBWGradedToPBWGraded_mk ..).symm⟩
  · rintro _ ⟨p, rfl⟩
    exact ⟨_, centerPBWGradedToPBWGraded_symmetrizationCenter hn p⟩

variable (R L)

/-- **The central elements of degree `n`, modulo those of lower degree, are the homogeneous Lie
invariants of degree `n`**, for `L` free over `R` and `n!` a unit in `R`: the isomorphism
`Z_n / Z_{n-1} ≃ S^n(L)^L` taking a central element to its PBW symbol. -/
noncomputable def centerPBWGradedInvariantIso [Module.Free R L] (n : ℕ)
    (hn : IsUnit (n.factorial : R)) :
    CenterPBWGradedPiece R L n ≃ₗ[R]
      (Subalgebra.toSubmodule (lieInvariants R L L) ⊓ homogeneousSubmodule R L n :
        Submodule R (SymmetricAlgebra R L)) :=
  (LinearEquiv.ofInjective _ (centerPBWGradedToPBWGraded_injective R L n)).trans <|
    (LinearEquiv.ofEq _ _ (range_centerPBWGradedToPBWGraded hn)).trans
      (LinearEquiv.ofInjective _ (invariantToPBWGraded_injective n)).symm

/-- **The isomorphism `Z_n / Z_{n-1} ≃ S^n(L)^L` is the PBW symbol**: the PBW image of the
invariant attached to a class of central elements is the degree-`n` class of those elements. -/
theorem centerPBWGradedInvariantIso_symbol [Module.Free R L] (n : ℕ)
    (hn : IsUnit (n.factorial : R)) (z : CenterPBWGradedPiece R L n) :
    centerPBWGradedToPBWGraded R L n z =
      pbwHomogeneousComponentMap R L n
        ⟨(centerPBWGradedInvariantIso R L n hn z : SymmetricAlgebra R L),
          (Submodule.mem_inf.mp (centerPBWGradedInvariantIso R L n hn z).2).2⟩ := by
  rw [← invariantToPBWGraded_apply,
    ← LinearEquiv.ofInjective_apply _ (h := invariantToPBWGraded_injective n)]
  simp only [centerPBWGradedInvariantIso, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]

/-- **The inverse of `Z_n / Z_{n-1} ≃ S^n(L)^L` is symmetrization**: a homogeneous invariant
corresponds to the class of its symmetrization, which is central. -/
theorem centerPBWGradedInvariantIso_symm_apply [Module.Free R L] (n : ℕ)
    (hn : IsUnit (n.factorial : R))
    (p : (Subalgebra.toSubmodule (lieInvariants R L L) ⊓ homogeneousSubmodule R L n :
      Submodule R (SymmetricAlgebra R L))) :
    (centerPBWGradedInvariantIso R L n hn).symm p =
      Submodule.Quotient.mk
        ⟨⟨pbwHomogeneousSymmetrization R L n hn ⟨p, (Submodule.mem_inf.mp p.2).2⟩,
            pbwHomogeneousSymmetrization_mem_center R L n hn (Submodule.mem_inf.mp p.2).1⟩,
          mem_centerPBWFiltration.mpr
            (pbwHomogeneousSymmetrization_mem_pbwFiltration R L n hn _)⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  apply invariantToPBWGraded_injective (R := R) (L := L) n
  rw [← centerPBWGradedToPBWGraded_symmetrizationCenter hn p, invariantToPBWGraded_apply,
    ← centerPBWGradedInvariantIso_symbol]
  -- The two sides are the symbols of the same central element, built twice.
  rfl

end TauCeti.UniversalEnvelopingAlgebra
