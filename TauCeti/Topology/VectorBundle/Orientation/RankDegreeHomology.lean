/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.Topology.VectorBundle.Thom.Orientation.LocalSystem

/-!
# The homology of the Thom pair in the rank degree, with orientation coefficients

Let `E → B` be a real vector bundle of rank `r = n + 1` over an arbitrary base, with Thom pair
`(E, E₀)`, `E₀` the complement of the zero section, and let `o(E)` be its integral orientation
local system (`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre over `b` is the
group of functions `σ` on the two orientations of `E_b` with `σ(-o) = -σ(o)`. This file computes the
first group of the Thom pair that does not vanish, with integral coefficients and without an
orientation of the bundle:

`Hᵣ(E, E₀; ℤ) ≅ H₀(B; o(E))`

(`TauCeti.thomPairSingularHomologyIsoTwistedHomology`). An orientation `o` of a fibre `E_b`
selects a local orientation of the fibre pair `(E_b, E_b ∖ {0})`, a generator of its homology in
degree `r` (`TauCeti.fiberLocalOrientation`), and the isomorphism sends the image of this generator
in `Hᵣ(E, E₀; ℤ)` to the class of the element of the fibre of `o(E)` over `b` with value `1` at
`o` (`TauCeti.thomPairSingularHomologyIsoTwistedHomology_hom_apply`). Reversing `o` changes the
sign of both. This is the bottom degree of the Thom isomorphism `Hₖ₊ᵣ(E, E₀; L) ≅ Hₖ(B; o(E) ⊗ L)`
with local coefficients. For an orientable bundle `o(E)` is trivial and `H₀(B; o(E)) ≅ H₀(B; ℤ)`;
for the Möbius line over the circle, `H₀(S¹; o(E)) ≅ ℤ/2`.

This is the identification that crossing the level of a Morse–Bott critical submanifold `C` of
index `λ` produces in the lowest degree: the relative homology of the attachment of the negative
disc bundle `ν⁻` along its sphere bundle is that of the Thom pair of `ν⁻`, so
`H_λ(M_{c+ε}, M_{c-ε}; ℤ) ≅ H₀(C; o(ν⁻))`.

## The proof

This is the integral case of the identification over any ring
`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`, which depends on
an orientation of the model fibre `F` through the identification of each fibre of `o(E)` with
`Hᵣ(E_b, E_b ∖ {0})`. Here that orientation is the one whose local orientation is the point class
`TauCeti.complZeroPairPointHom` of `1`. Read in the trivialization at `b`, the local orientation
selected by `o` is then the point class carried to the fibre when `o` is read as this orientation,
and its opposite otherwise, which gives the values on the fibre classes.

## Main definitions and results

* `TauCeti.fiberLocalOrientation`: the local orientation of the fibre pair `(E_b, E_b ∖ {0})`
  selected by an orientation of `E_b`; it does not depend on the trivialization reading it
  (`TauCeti.fiberLocalOrientation_eq_map`).
* `TauCeti.thomPairSingularHomologyIsoTwistedHomology`: `Hᵣ(E, E₀; ℤ) ≅ H₀(B; o(E))`.
* `TauCeti.thomPairSingularHomologyIsoTwistedHomology_hom_apply`: it sends the local orientation of
  the fibre over `b` selected by `o` to the element with value `1` at `o`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4, and §12 (twisted coefficients).
* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients) and Section 4.D,
  Theorem 4D.10 and its proof.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse theory: lecture notes*, 2006,
  Theorem 15.4.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module AlgebraicTopology Topology

universe w

namespace TauCeti

section LocalOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ} (hF : finrank ℝ F = n + 1)

/-- The local orientation of the fibre pair `(E_b, E_b ∖ {0})` selected by an orientation of `E_b`,
read through the trivialization at `b`. -/
def fiberLocalOrientation (b : B) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    LocalOrientation (E b) 0 (n + 1) :=
  ((trivializationAt F E b).mapOrientation (Fin (n + 1)) (mem_baseSet_trivializationAt F E b) o
    |>.localOrientation hF).map
    ((trivializationAt F E b).continuousLinearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).complZeroPairIso.symm

/-- Any linear trivialization at `b` reads the same local orientation. -/
theorem fiberLocalOrientation_eq_map (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B}
    (hb : b ∈ e.baseSet) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    fiberLocalOrientation hF b o =
      ((e.mapOrientation (Fin (n + 1)) hb o).localOrientation hF).map
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.symm := by
  set e₀ := trivializationAt F E b
  have hb₀ : b ∈ e₀.baseSet := mem_baseSet_trivializationAt F E b
  set c := e₀.coordChangeL ℝ e b
  rw [fiberLocalOrientation, e₀.mapOrientation_eq_map_coordChangeL e hb₀ hb,
    Orientation.localOrientation_map c _ hF hF,
    ← e₀.continuousLinearEquivAt_trans_coordChangeL ℝ e hb₀ hb,
    ContinuousLinearEquiv.complZeroPairIso_trans, ← LocalOrientation.map_trans]
  congr 1
  rw [Iso.trans_symm, ← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

@[simp]
theorem fiberLocalOrientation_neg (b : B) (o : Orientation ℝ (E b) (Fin (n + 1))) :
    fiberLocalOrientation hF b (-o) = -fiberLocalOrientation hF b o := by
  simp [fiberLocalOrientation]

end LocalOrientation

section Twisted

open VectorBundleOrientationCover LocalCoefficientSystem

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ} (hF : finrank ℝ F = n + 1)

/-- An orientation of the model fibre selecting the point class
`TauCeti.complZeroPairPointHom` of `1` (`TauCeti.localOrientation_modelOrientation`). -/
private def modelOrientation : Orientation ℝ F (Fin (n + 1)) :=
  (Orientation.localOrientationEquiv hF).symm
    ⟨_, isLocalOrientation_complZeroPairPointHom_one F (n + 1) hF⟩

private theorem localOrientation_modelOrientation :
    ((modelOrientation hF).localOrientation hF).val =
      complZeroPairPointHom (ModuleCat.of ℤ (ULift.{w} ℤ)) F (n + 1) hF (ULift.up 1) :=
  congrArg Subtype.val (Orientation.localOrientation_localOrientationEquiv_symm hF _)

omit [FiniteDimensional ℝ F] in
variable (F E) in
/-- **The homology of the Thom pair in the rank degree, with orientation coefficients**: for a
real vector bundle `E → B` of rank `r = n + 1`, `Hᵣ(E, E₀; ℤ) ≅ H₀(B; o(E))`, the zeroth homology
of the base with coefficients in the orientation local system of `E`. It is the integral case of
`TauCeti.VectorBundleOrientationCover.thomPairSingularHomologyIsoTwistedHomology₀`, for the
orientation of the model fibre selecting the point class. -/
def thomPairSingularHomologyIsoTwistedHomology :
    (thomPair F E).singularHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) ≅
      twistedHomology.{0, w, 0}
        (signLocalSystem F E ℤ ((Fintype.card_fin (n + 1)).trans hF.symm)) 0 :=
  have := FiniteDimensional.of_finrank_eq_succ hF
  eqToIso (congrArg ((thomPair F E).singularHomology _) hF.symm) ≪≫
    thomPairSingularHomologyIsoTwistedHomology₀ ℤ E _ (modelOrientation hF)

/-- The degree of the point class may be rewritten along an equation, through the identification
of the homology groups in equal degrees. -/
private theorem complZeroPairPointHom_comp_eqToHom {X : TopPair} {k k' : ℕ} (hk : k = k')
    (hd : finrank ℝ F = k) (hd' : finrank ℝ F = k')
    (f : TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F) ⟶ X) :
    complZeroPairPointHom (ModuleCat.of ℤ (ULift.{w} ℤ)) F k hd ≫
        TopPair.singularHomologyMap f (ModuleCat.of ℤ (ULift.{w} ℤ)) k ≫
          eqToHom (by rw [hk]) =
      complZeroPairPointHom (ModuleCat.of ℤ (ULift.{w} ℤ)) F k' hd' ≫
        TopPair.singularHomologyMap f (ModuleCat.of ℤ (ULift.{w} ℤ)) k' := by
  subst hk
  simp

omit [FiniteDimensional ℝ F] in
/-- The isomorphism sends the class of the local orientation of the fibre over `b` selected by an
orientation `o` of `E_b` to the class of the element of the fibre of `o(E)` with value `1` at
`o`. -/
theorem thomPairSingularHomologyIsoTwistedHomology_hom_apply (b : B)
    (o : Orientation ℝ (E b) (Fin (n + 1))) :
    (thomPairSingularHomologyIsoTwistedHomology F E hF).hom
        (TopPair.singularHomologyMap (fiberThomPairMap F E b) (ModuleCat.of ℤ (ULift.{w} ℤ))
          (n + 1) (fiberLocalOrientation hF b o).val) =
      ιTwistedHomology₀ (signLocalSystem F E ℤ ((Fintype.card_fin (n + 1)).trans hF.symm)) b
        ((signLocalSystemFiberEquiv ((Fintype.card_fin (n + 1)).trans hF.symm) o).symm 1) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  set hι := (Fintype.card_fin (n + 1)).trans hF.symm
  set M := ModuleCat.of ℤ (ULift.{w} ℤ)
  set e := trivializationAt F E b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt F E b
  -- It suffices to treat the orientation that `e` reads as the model orientation.
  suffices h : ∀ o, e.mapOrientation (Fin (n + 1)) hb o = modelOrientation hF →
      (thomPairSingularHomologyIsoTwistedHomology F E hF).inv
          (ιTwistedHomology₀ (signLocalSystem F E ℤ hι) b
            ((signLocalSystemFiberEquiv hι o).symm 1)) =
        TopPair.singularHomologyMap (fiberThomPairMap F E b) M (n + 1)
          (fiberLocalOrientation hF b o).val by
    rcases Orientation.eq_or_eq_neg (e.mapOrientation (Fin (n + 1)) hb o) (modelOrientation hF)
      (Nat.card_eq_fintype_card.trans hι) with ho | ho
    · rw [← h o ho, Iso.inv_hom_id_apply]
    · have hneg : (signLocalSystemFiberEquiv hι (-o)).symm (1 : ℤ) =
          -(signLocalSystemFiberEquiv hι o).symm 1 :=
        LinearMap.congr_fun (signLocalSystemFiberEquiv_neg_symm hι o) 1
      have h' := h (-o) (by
        rw [Bundle.Trivialization.mapOrientation_neg, ho]; exact neg_neg (modelOrientation hF))
      rw [hneg, map_neg, map_neg, fiberLocalOrientation_neg, LocalOrientation.coe_neg, map_neg,
        neg_inj] at h'
      rw [← h', Iso.inv_hom_id_apply]
  intro o ho
  have hω : (e.mapOrientation (Fin (n + 1)) hb).symm (modelOrientation hF) = o := by
    rw [Equiv.symm_apply_eq, ho]
  have h2 : (fiberLocalOrientation hF b o).val =
      TopPair.singularHomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv M (n + 1)
        (complZeroPairPointHom M F (n + 1) hF (ULift.up 1)) := by
    rw [fiberLocalOrientation_eq_map hF e hb, LocalOrientation.coe_map, ho,
      localOrientation_modelOrientation, Iso.symm_hom]
  have h3 := congrArg (fun f ↦ f (ULift.up 1)) (complZeroPairPointHom_comp_eqToHom hF rfl hF
    ((e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.inv ≫ fiberThomPairMap F E b))
  simp only [TopPair.singularHomologyMap_comp, ConcreteCategory.comp_apply] at h3
  rw [h2, ← h3, thomPairSingularHomologyIsoTwistedHomology, Iso.trans_inv, eqToIso.inv,
    ← ConcreteCategory.comp_apply,
    ιTwistedHomology₀_thomPairSingularHomologyIsoTwistedHomology₀_inv_assoc,
    signLocalSystemFiberIsoSingularHomology_hom ℤ hι _ e hb, hω]
  simp

end Twisted

end TauCeti
