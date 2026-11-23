/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Constant
public import TauCeti.AlgebraicTopology.Singular.Twisted.Sign
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem

/-!
# Zeroth homology with coefficients in the orientation local system

Let `E → B` be a real vector bundle over a connected base and `o(E)` its orientation local system
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `b` is a copy of `R`
with the two orientations of `E_b` as its generators. Its zeroth homology `H₀(B; o(E))` sees
whether `E` is orientable:

* if `E` has an orientation, it trivializes `o(E)`, and if moreover `B` is path-connected,
  `H₀(B; o(E)) ≅ R` (`TauCeti.VectorBundleOrientation.twistedHomology₀Equiv`); this
  identification sends the class of an element of any fibre to its value at the chosen
  orientation of that fibre;
* if `E` is not orientable and `B` is locally path-connected, some loop reverses the orientation of
  a fibre
  (`VectorBundleOrientationCover.exists_monodromyRepresentation_signLocalSystem_eq_neg_one`),
  and `H₀(B; o(E)) ≅ R ⧸ 2R`
  (`TauCeti.VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo`); this
  identification sends the class of an element of any fibre to the residue of its value at
  either orientation of that fibre.

When `2 ≠ 0` in `R` and `B` is locally path-connected, `H₀(B; o(E))` is therefore isomorphic
to `R` exactly when `E` is orientable
(`TauCeti.VectorBundleOrientation.nonempty_iff_nonempty_twistedHomology₀_linearEquiv`); with
integer coefficients it is `ℤ` or `ℤ/2`. For instance, for the Möbius line over the circle,
which is not orientable, it is `ℤ/2`, not the `ℤ` of constant coefficients. This group is the
coefficient group in the bottom degree of the Thom isomorphism `H_{n+r}(E, E₀; ℤ) ≅ H_n(B; o(E))`
of a rank `r` bundle, for instance across the level of a Morse–Bott critical submanifold, where
`E` is its negative normal bundle.

## Main definitions

* `TauCeti.VectorBundleOrientation.twistedHomology₀Equiv`: `H₀(B; o(E)) ≅ R` for an oriented
  bundle over a path-connected base.
* `TauCeti.VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo`: `H₀(B; o(E)) ≅ R ⧸ 2R`
  for a non-orientable bundle over a connected, locally path-connected base.

## Main results

* `TauCeti.VectorBundleOrientation.nonempty_iff_nonempty_twistedHomology₀_linearEquiv`: if
  `2 ≠ 0` in `R`, a bundle over a connected, locally path-connected base is orientable exactly
  when `H₀(B; o(E); R) ≅ R`.

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

/-- **Zeroth homology of a non-orientable orientation system.** Over a connected, locally
path-connected base, if `E` is not orientable, `H₀(B; o(E)) ≅ R ⧸ 2R`. It sends the class of an
element of the fibre over any point `b'` to the residue of its value at either orientation of
`E_b'`; the orientation `o` of `E_b` is only used in the construction
(`twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀`, `twistedHomology₀EquivQuotientTwo_eq`). -/
def twistedHomology₀EquivQuotientTwo [ConnectedSpace B] [LocallyPathConnectedSpace B]
    (h : IsEmpty (VectorBundleOrientation F E ι)) {b : B} (o : Orientation ℝ (E b) ι) :
    twistedHomology.{u, uB, max uE uι u} (signLocalSystem F E R hι) 0 ≃ₗ[R]
      R ⧸ Ideal.span {(2 : R)} :=
  haveI : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  LocalCoefficientSystem.twistedHomology₀EquivQuotientTwo.{u, uB, max uE uι u} _ b
    (monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one hι b)
    (exists_monodromyRepresentation_signLocalSystem_eq_neg_one hι h b).choose_spec ≪≫ₗ
    Submodule.Quotient.equiv _ _ (signLocalSystemFiberEquiv hι o) (by simp [Submodule.map_smul''])

/-- The identification of `H₀(B; o(E))` with `R ⧸ 2R` sends the class of an element of the fibre
over `b` to the residue of its value at `o`. -/
@[simp]
theorem twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀_self [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h : IsEmpty (VectorBundleOrientation F E ι)) {b : B}
    (o : Orientation ℝ (E b) ι) (a : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b)) :
    twistedHomology₀EquivQuotientTwo hι h o (ιTwistedHomology₀ (signLocalSystem F E R hι) b a) =
      Ideal.Quotient.mk _ (signLocalSystemFiberEquiv hι o a) := by
  have : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  rw [twistedHomology₀EquivQuotientTwo, LinearEquiv.trans_apply,
    LocalCoefficientSystem.twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀.{u, uB, max uE uι u}]
  simp

/-- The identification of `H₀(B; o(E))` with `R ⧸ 2R` sends the class of an element of the fibre
over any point `b'` to the residue of its value at any orientation `o'` of `E_b'`. -/
theorem twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀ [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h : IsEmpty (VectorBundleOrientation F E ι)) {b b' : B}
    (o : Orientation ℝ (E b) ι) (o' : Orientation ℝ (E b') ι)
    (a : (signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b')) :
    twistedHomology₀EquivQuotientTwo hι h o (ιTwistedHomology₀ (signLocalSystem F E R hι) b' a) =
      Ideal.Quotient.mk _ (signLocalSystemFiberEquiv hι o' a) := by
  have : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  -- Transport `a` to `b` along a path `γ`. This changes its value by a sign, which vanishes
  -- modulo `2`.
  let γ : FundamentalGroupoid.mk b' ⟶ FundamentalGroupoid.mk b :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath b' b)
  rw [← map_ιTwistedHomology₀_apply.{u, uB, max uE uι u} _ γ a,
    twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀_self,
    signLocalSystemFiberEquiv_apply, signLocalSystemObjEquiv_map_apply]
  -- The lift of `γ⁻¹` starting at `o` ends at `o'` or at `-o'`.
  set e := (isCoveringMap_proj hι).monodromy (inv γ)
    (⟨⟨b, o⟩, rfl⟩ : (proj ⁻¹' {b} : Set (VectorBundleOrientationCover F E ι)))
  rcases eq_or_eq_deck hι (p := ⟨b', o'⟩) (q := e.val) e.property with he | he
  · rw [show e = ⟨⟨b', o'⟩, rfl⟩ from Subtype.ext he, ← signLocalSystemFiberEquiv_apply]
  · rw [show e = ⟨⟨b', -o'⟩, rfl⟩ from Subtype.ext (he.trans (deck_apply _)),
      ← signLocalSystemFiberEquiv_apply, signLocalSystemFiberEquiv_neg, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.2 ⟨-signLocalSystemFiberEquiv hι o' a, by ring⟩

/-- The inverse identification sends the residue of `r` to the class of the element of the fibre
over `b` whose value at `o` is `r`. -/
@[simp]
theorem twistedHomology₀EquivQuotientTwo_symm_mk_self [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h : IsEmpty (VectorBundleOrientation F E ι)) {b : B}
    (o : Orientation ℝ (E b) ι) (r : R) :
    (twistedHomology₀EquivQuotientTwo hι h o).symm (Ideal.Quotient.mk _ r) =
      ιTwistedHomology₀ (signLocalSystem F E R hι) b ((signLocalSystemFiberEquiv hι o).symm r) :=
  (LinearEquiv.symm_apply_eq _).2 (by
    rw [twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀_self, LinearEquiv.apply_symm_apply])

/-- The inverse identification sends the residue of `r` to the class of the element of the fibre
over any point `b'` whose value at any orientation `o'` of `E_b'` is `r`. -/
theorem twistedHomology₀EquivQuotientTwo_symm_mk [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h : IsEmpty (VectorBundleOrientation F E ι)) {b b' : B}
    (o : Orientation ℝ (E b) ι) (o' : Orientation ℝ (E b') ι) (r : R) :
    (twistedHomology₀EquivQuotientTwo hι h o).symm (Ideal.Quotient.mk _ r) =
      ιTwistedHomology₀ (signLocalSystem F E R hι) b' ((signLocalSystemFiberEquiv hι o').symm r) :=
  (LinearEquiv.symm_apply_eq _).2 (by
    rw [twistedHomology₀EquivQuotientTwo_ιTwistedHomology₀ hι h o o',
      LinearEquiv.apply_symm_apply])

/-- The identification of `H₀(B; o(E))` with `R ⧸ 2R` does not depend on the point and orientation
used to construct it. -/
theorem twistedHomology₀EquivQuotientTwo_eq [ConnectedSpace B] [LocallyPathConnectedSpace B]
    (h : IsEmpty (VectorBundleOrientation F E ι)) {b b' : B} (o : Orientation ℝ (E b) ι)
    (o' : Orientation ℝ (E b') ι) :
    twistedHomology₀EquivQuotientTwo (R := R) hι h o = twistedHomology₀EquivQuotientTwo hι h o' :=
  LinearEquiv.symm_bijective.injective <| LinearEquiv.ext fun r ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [twistedHomology₀EquivQuotientTwo_symm_mk hι h o o' r,
      twistedHomology₀EquivQuotientTwo_symm_mk_self]

end VectorBundleOrientationCover

namespace VectorBundleOrientation

/-- **Zeroth homology of an oriented orientation system.** Over a path-connected base, an
orientation `o` of `E` identifies `H₀(B; o(E))` with `R`. It sends the class of an element of the
fibre over any point `b'` to its value at the orientation `o b'` of `E_b'`; the basepoint `b` is
only used in the construction (`twistedHomology₀Equiv_ιTwistedHomology₀`,
`twistedHomology₀Equiv_eq`). -/
def twistedHomology₀Equiv [PathConnectedSpace B] (o : VectorBundleOrientation F E ι) (b : B) :
    twistedHomology.{u, uB, max uE uι u} (VectorBundleOrientationCover.signLocalSystem F E R hι) 0
      ≃ₗ[R] R :=
  haveI := isTrivial_monodromyRepresentation_of_iso_constant (signLocalSystemIso (R := R) hι o) b
  twistedHomology₀EquivOfIsTrivial.{u, uB, max uE uι u} _ b ≪≫ₗ
    VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b)

omit [FiniteDimensional ℝ F] in
/-- The identification of `H₀(B; o(E))` with `R` given by `o` sends the class of an element of the
fibre over any point `b'` to its value at the orientation `o b'`. In particular, it does not depend
on the basepoint `b`. -/
@[simp]
theorem twistedHomology₀Equiv_ιTwistedHomology₀ [PathConnectedSpace B]
    (o : VectorBundleOrientation F E ι) (b b' : B)
    (a : (VectorBundleOrientationCover.signLocalSystem F E R hι).obj (FundamentalGroupoid.mk b')) :
    twistedHomology₀Equiv hι o b
      (ιTwistedHomology₀ (VectorBundleOrientationCover.signLocalSystem F E R hι) b' a) =
      VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b') a := by
  have := isTrivial_monodromyRepresentation_of_iso_constant (signLocalSystemIso (R := R) hι o) b
  -- Transport `a` to the basepoint along a path `γ`; transport factors through the
  -- trivialization given by `o`.
  let γ : FundamentalGroupoid.mk b' ⟶ FundamentalGroupoid.mk b :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath b' b)
  rw [← map_ιTwistedHomology₀_apply.{u, uB, max uE uι u} _ γ a, twistedHomology₀Equiv,
    LinearEquiv.trans_apply, twistedHomology₀EquivOfIsTrivial_ιTwistedHomology₀,
    map_eq_of_iso_constant (signLocalSystemIso hι o) γ]
  exact congrArg ULift.down ((signLocalSystemIso_hom_app_apply hι o b _).symm.trans
    ((((signLocalSystemIso hι o).app _).inv_hom_id_apply _).trans
      (signLocalSystemIso_hom_app_apply hι o b' a)))

omit [FiniteDimensional ℝ F] in
/-- The inverse identification sends `r` to the class of the element of the fibre over any point
`b'` whose value at the orientation `o b'` is `r`. -/
theorem twistedHomology₀Equiv_symm_apply [PathConnectedSpace B]
    (o : VectorBundleOrientation F E ι) (b b' : B) (r : R) :
    (twistedHomology₀Equiv hι o b).symm r =
      ιTwistedHomology₀ (VectorBundleOrientationCover.signLocalSystem F E R hι) b'
        ((VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b')).symm r) :=
  (LinearEquiv.symm_apply_eq _).2 (by
    rw [twistedHomology₀Equiv_ιTwistedHomology₀, LinearEquiv.apply_symm_apply])

omit [FiniteDimensional ℝ F] in
/-- The inverse identification sends `r` to the class of the element of the fibre over `b` whose
value at the orientation `o b` is `r`. -/
@[simp]
theorem twistedHomology₀Equiv_symm_apply_self [PathConnectedSpace B]
    (o : VectorBundleOrientation F E ι) (b : B) (r : R) :
    (twistedHomology₀Equiv hι o b).symm r =
      ιTwistedHomology₀ (VectorBundleOrientationCover.signLocalSystem F E R hι) b
        ((VectorBundleOrientationCover.signLocalSystemFiberEquiv hι (o b)).symm r) :=
  twistedHomology₀Equiv_symm_apply hι o b b r

omit [FiniteDimensional ℝ F] in
/-- The identification of `H₀(B; o(E))` with `R` given by `o` does not depend on the basepoint
used to construct it. -/
theorem twistedHomology₀Equiv_eq [PathConnectedSpace B] (o : VectorBundleOrientation F E ι)
    (b b' : B) :
    twistedHomology₀Equiv (R := R) hι o b = twistedHomology₀Equiv hι o b' :=
  LinearEquiv.symm_bijective.injective <| LinearEquiv.ext fun r ↦ by
    rw [twistedHomology₀Equiv_symm_apply hι o b b r, twistedHomology₀Equiv_symm_apply hι o b' b r]

/-- **Orientability from zeroth twisted homology.** If `2 ≠ 0` in `R`, a real vector bundle over a
connected, locally path-connected base is orientable exactly when the zeroth homology of its
orientation local system with coefficients in `R` is isomorphic to `R`. Otherwise it is `R ⧸ 2R`
(`TauCeti.VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo`). -/
theorem nonempty_iff_nonempty_twistedHomology₀_linearEquiv [ConnectedSpace B]
    [LocallyPathConnectedSpace B] (h2 : (2 : R) ≠ 0) :
    Nonempty (VectorBundleOrientation F E ι) ↔
      Nonempty (twistedHomology.{u, uB, max uE uι u}
        (VectorBundleOrientationCover.signLocalSystem F E R hι) 0 ≃ₗ[R] R) := by
  have : PathConnectedSpace B := PathConnectedSpace.of_locallyPathConnectedSpace
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  refine ⟨fun ⟨o⟩ ↦ ⟨twistedHomology₀Equiv hι o b⟩, fun ⟨φ⟩ ↦ ?_⟩
  by_contra h
  obtain ⟨q, -⟩ := VectorBundleOrientationCover.surjective_proj (F := F) (E := E) hι b
  -- Otherwise `H₀(B; o(E)) ≅ R ⧸ 2R`, whose elements are killed by `2`, unlike `1 : R`.
  let ψ := (VectorBundleOrientationCover.twistedHomology₀EquivQuotientTwo hι (not_nonempty_iff.1 h)
    q.orientation).symm ≪≫ₗ φ
  obtain ⟨n, hn⟩ := Ideal.Quotient.mk_surjective (ψ.symm 1)
  have h2' : (2 : R) • ψ.symm 1 = 0 := by
    rw [← hn, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self 2)
  have := congrArg ψ h2'
  rw [map_smul, LinearEquiv.apply_symm_apply, map_zero] at this
  exact h2 (by simpa using this)

end VectorBundleOrientation

end TauCeti
