/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Constant
public import TauCeti.AlgebraicTopology.Singular.Twisted.Sign
public import TauCeti.Topology.Homotopy.Monodromy.Basic
public import TauCeti.Topology.IsLocalHomeomorph
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem

/-!
# Zeroth homology with coefficients in the orientation local system

Let `E → B` be a real vector bundle over a connected base and `o(E)` its orientation local system
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `b` is a copy of `R`
with the two orientations of `E_b` as its generators. Its zeroth homology `H₀(B; o(E))` sees
whether `E` is orientable:

* if `E` has an orientation, it trivializes `o(E)`, and `H₀(B; o(E)) ≅ R`
  (`TauCeti.VectorBundleOrientation.twistedHomology₀Equiv`);
* if `E` is not orientable and `B` is locally path-connected, some loop reverses the orientation of
  a fibre
  (`VectorBundleOrientationCover.exists_monodromyRepresentation_signLocalSystem_eq_neg_one`),
  and `H₀(B; o(E)) ≅ R ⧸ 2R`
  (`TauCeti.VectorBundleOrientationCover.twistedHomology₀EquivOfIsEmpty`).

With integer coefficients, `H₀(B; o(E))` is therefore `ℤ` or `ℤ/2`, and it is isomorphic to `ℤ`
exactly when `E` is orientable
(`TauCeti.VectorBundleOrientation.nonempty_iff_nonempty_twistedHomology₀_linearEquiv_int`). For
instance, for the Möbius line over the circle, which is not orientable, it is `ℤ/2`, not the `ℤ`
of constant coefficients. This group is
the coefficient group in the bottom degree of the Thom isomorphism
`H_{n+r}(E, E₀; ℤ) ≅ H_n(B; o(E))` of a rank `r` bundle, for instance across the level of a
Morse–Bott critical submanifold, where `E` is its negative normal bundle.

The non-orientable case uses that the orientation double cover of a non-orientable bundle over a
connected base is connected (`TauCeti.VectorBundleOrientation.nonempty_iff_not_connectedSpace`),
hence path-connected, so a path in the cover joins the two orientations of a fibre; it projects to
a loop whose monodromy exchanges them.

## Main definitions

* `TauCeti.VectorBundleOrientation.twistedHomology₀Equiv`: `H₀(B; o(E)) ≅ R` for an oriented
  bundle over a path-connected base.
* `TauCeti.VectorBundleOrientationCover.twistedHomology₀EquivOfIsEmpty`: `H₀(B; o(E)) ≅ R ⧸ 2R`
  for a non-orientable bundle over a connected, locally path-connected base.

## Main results

* `TauCeti.VectorBundleOrientation.nonempty_iff_nonempty_twistedHomology₀_linearEquiv_int`: a
  bundle over a connected, locally path-connected base is orientable exactly when
  `H₀(B; o(E); ℤ) ≅ ℤ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (the orientation system and zeroth homology with
  local coefficients).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover and twisted coefficients).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

universe u uB uE uι

variable {B : Type uB} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type uι} [Fintype ι] {R : Type u} [CommRing R] (hι : Fintype.card ι = finrank ℝ F)

namespace TauCeti

open LocalCoefficientSystem

namespace VectorBundleOrientationCover

omit [FiniteDimensional ℝ F] in
/-- Every loop at `b` acts by `1` or by `-1` on the fibre of the orientation local system over
`b`. -/
theorem monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one (b : B)
    (g : FundamentalGroup (TopCat.of B) b) :
    monodromyRepresentation (signLocalSystem F E R hι) b g = 1 ∨
      monodromyRepresentation (signLocalSystem F E R hι) b g = -1 := by
  rw [signLocalSystem_eq]
  exact (isCoveringMap_proj hι).monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one
    (hσ := proj_comp_deck) deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) g

/-- **A non-orientable bundle has an orientation-reversing loop.** Over a connected, locally
path-connected base, if `E` is not orientable, some loop at `b` acts by `-1` on the fibre of the
orientation local system over `b`. -/
theorem exists_monodromyRepresentation_signLocalSystem_eq_neg_one [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h : IsEmpty (VectorBundleOrientation F E ι)) (b : B) :
    ∃ g : FundamentalGroup (TopCat.of B) b,
      monodromyRepresentation (signLocalSystem F E R hι) b g = -1 := by
  have hp := isCoveringMap_proj (F := F) (E := E) hι
  have : ConnectedSpace (VectorBundleOrientationCover F E ι) :=
    not_not.1 fun hc ↦
      h.false ((VectorBundleOrientation.nonempty_iff_not_connectedSpace hι).2 hc).some
  have : LocallyPathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace (VectorBundleOrientationCover F E ι) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  -- A path in the cover from a point `q` over `b` to `deck q` projects to a loop at `b` whose
  -- monodromy carries `q` to `deck q`.
  obtain ⟨q, hq⟩ := surjective_proj (F := F) (E := E) hι b
  obtain ⟨g, hg⟩ := hp.exists_monodromy_eq_of_joined (X := TopCat.of B) (e := ⟨q, hq⟩)
    (e' := ⟨deck q, (proj_deck q).trans hq⟩) (PathConnectedSpace.joined _ _)
  rw [signLocalSystem_eq]
  refine ⟨g, hp.monodromyRepresentation_signLocalSystem_eq_neg_one (hσ := proj_comp_deck)
    deck_ne_self (fun _ _ h ↦ eq_or_eq_deck hι h) (e := ⟨q, hq⟩) (hg.trans (Subtype.ext ?_))⟩
  exact (Function.fiberMap_apply_coe _ proj_comp_deck b ⟨q, hq⟩).symm

/-- **Zeroth homology of a non-orientable orientation system.** Over a connected, locally
path-connected base, if `E` is not orientable, `H₀(B; o(E)) ≅ R ⧸ 2R`. It sends the class of an
element of the fibre over `b` to the residue of its value at the orientation `o` of `E_b`. -/
def twistedHomology₀EquivOfIsEmpty [ConnectedSpace B] [LocallyPathConnectedSpace B]
    (h : IsEmpty (VectorBundleOrientation F E ι)) {b : B} (o : Orientation ℝ (E b) ι) :
    twistedHomology.{u, uB, max uE uι u} (signLocalSystem F E R hι) 0 ≃ₗ[R]
      R ⧸ Ideal.span {(2 : R)} :=
  haveI : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  twistedHomology₀EquivQuotientTwo.{u, uB, max uE uι u} _ b (signLocalSystemFiberEquiv hι o)
    (monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one hι b)
    (exists_monodromyRepresentation_signLocalSystem_eq_neg_one hι h b).choose_spec

/-- The identification of `H₀(B; o(E))` with `R ⧸ 2R` sends the class of an element of the fibre
over `b` to the residue of its value at `o`. -/
@[simp]
theorem twistedHomology₀EquivOfIsEmpty_ιTwistedHomology₀ [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h : IsEmpty (VectorBundleOrientation F E ι)) {b : B}
    (o : Orientation ℝ (E b) ι) (a : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    twistedHomology₀EquivOfIsEmpty hι h o (ιTwistedHomology₀ (signLocalSystem F E R hι) b a) =
      Ideal.Quotient.mk _ (signLocalSystemFiberEquiv hι o a) :=
  haveI : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀.{u, uB, max uE uι u} _ _ _ _ _ a

end VectorBundleOrientationCover

namespace VectorBundleOrientation

/-- **Zeroth homology of an oriented orientation system.** Over a path-connected base, an
orientation `o` of `E` identifies `H₀(B; o(E))` with `R`. It sends the class of an element of the
fibre over `b` to its value at the orientation `o b` of `E_b`. -/
def twistedHomology₀Equiv [PathConnectedSpace B] (o : VectorBundleOrientation F E ι) (b : B) :
    twistedHomology.{u, uB, max uE uι u} (VectorBundleOrientationCover.signLocalSystem F E R hι) 0
      ≃ₗ[R] R :=
  haveI := isTrivial_monodromyRepresentation_of_iso_constant (signLocalSystemIso (R := R) hι o) b
  twistedHomology₀EquivOfIsTrivial.{u, uB, max uE uι u} _ b ≪≫ₗ
    VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b)

omit [FiniteDimensional ℝ F] in
/-- The identification of `H₀(B; o(E))` with `R` given by `o` sends the class of an element of the
fibre over `b` to its value at the orientation `o b`. -/
@[simp]
theorem twistedHomology₀Equiv_ιTwistedHomology₀ [PathConnectedSpace B]
    (o : VectorBundleOrientation F E ι) (b : B)
    (a : (VectorBundleOrientationCover.signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    twistedHomology₀Equiv hι o b
      (ιTwistedHomology₀ (VectorBundleOrientationCover.signLocalSystem F E R hι) b a) =
      VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b) a := by
  have := isTrivial_monodromyRepresentation_of_iso_constant (signLocalSystemIso (R := R) hι o) b
  rw [twistedHomology₀Equiv, LinearEquiv.trans_apply,
    twistedHomology₀EquivOfIsTrivial_ιTwistedHomology₀]

/-- **Orientability from zeroth twisted homology.** A real vector bundle over a connected, locally
path-connected base is orientable exactly when the zeroth homology of its integral orientation
local system is isomorphic to `ℤ`; otherwise that homology is `ℤ/2`. -/
theorem nonempty_iff_nonempty_twistedHomology₀_linearEquiv_int [ConnectedSpace B]
    [LocallyPathConnectedSpace B] :
    Nonempty (VectorBundleOrientation F E ι) ↔
      Nonempty (twistedHomology.{0, uB, max uE uι}
        (VectorBundleOrientationCover.signLocalSystem F E ℤ hι) 0 ≃ₗ[ℤ] ℤ) := by
  have : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  refine ⟨fun ⟨o⟩ ↦ ⟨twistedHomology₀Equiv hι o b⟩, fun ⟨φ⟩ ↦ ?_⟩
  by_contra h
  obtain ⟨q, -⟩ := VectorBundleOrientationCover.surjective_proj (F := F) (E := E) hι b
  -- Otherwise `H₀(B; o(E)) ≅ ℤ ⧸ 2ℤ`, whose elements are killed by `2`, unlike `1 : ℤ`.
  let ψ := (VectorBundleOrientationCover.twistedHomology₀EquivOfIsEmpty hι (not_nonempty_iff.1 h)
    q.orientation).symm ≪≫ₗ φ
  obtain ⟨n, hn⟩ := Ideal.Quotient.mk_surjective (ψ.symm 1)
  have h2 : (2 : ℤ) • ψ.symm 1 = 0 := by
    rw [← hn, ← map_zsmul, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2)
  have := congrArg ψ h2
  rw [map_zsmul, LinearEquiv.apply_symm_apply, map_zero] at this
  norm_num at this

end VectorBundleOrientation

end TauCeti
