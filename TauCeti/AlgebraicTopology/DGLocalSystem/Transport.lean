/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.HomotopyInvariance

/-!
# Transport is a quasi-isomorphism of DG local systems

An equivariant homotopy equivalence induces a quasi-isomorphism of the DG right modules of cubical
chains (`TauCeti.isQuasiIso_cubicalChainModuleMap`).  For a transitive lifting function `Φ` of
`p : E → B`, transport `F' → F` is a strictly equivariant homotopy equivalence, so the strict
morphism `C_*(F') → C_*(F)_Φ` of DG local systems is a quasi-isomorphism
(`TauCeti.isQuasiIso_transportLocalSystemHom`).  Two transitive lifting functions `Φ₀`, `Φ₁` are
therefore compared by the specified zigzag of strict quasi-isomorphisms
`C_*(F)_{Φ₀} ← C_*(F') → C_*(F)_{Φ₁}` (`TauCeti.liftingLocalSystemRoof`), with no homotopy
between the lifting functions.

Both legs of the zigzag are quasi-isomorphisms, so any functor `L` out of DG local systems that
inverts quasi-isomorphisms turns it into an isomorphism
`L(C_*(F)_{Φ₀}) ≅ L(C_*(F)_{Φ₁})` (`TauCeti.liftingLocalSystemIso`). For a localization functor
at the quasi-isomorphisms this is the isomorphism in the derived category of DG local systems; for
the cohomology functor (`TauCeti.DGRightModuleCat.quasiIsos_isInvertedBy_cohomologyFunctor`) it is
an isomorphism of cohomology modules over `H_*(Ω_b B)`. The comparison is the only isomorphism
compatible with the transports from `C_*(F')`, which does not depend on a lifting function. It
is the identity for `Φ₀ = Φ₁`, and comparisons compose, so the objects `L(C_*(F)_Φ)` for the
transitive lifting functions `Φ` are canonically identified.

## Main results

* `TauCeti.isQuasiIso_transportLocalSystemHom`: transport is a quasi-isomorphism.
* `TauCeti.liftingLocalSystemRoof`: the zigzag comparing two transitive lifting functions, a
  right fraction for the quasi-isomorphisms.
* `TauCeti.liftingLocalSystemIso`: the comparison `L(C_*(F)_{Φ₀}) ≅ L(C_*(F)_{Φ₁})`, the image of
  the zigzag (`TauCeti.liftingLocalSystemIso_hom`).
* `TauCeti.eq_liftingLocalSystemIso`: it is the unique isomorphism compatible with the
  transports.
* `TauCeti.liftingLocalSystemIso_self`, `TauCeti.liftingLocalSystemIso_symm`,
  `TauCeti.liftingLocalSystemIso_trans_liftingLocalSystemIso`: identity, inverse and composition.
* `TauCeti.mapIso_liftingLocalSystemIso`: naturality in `L`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite ContinuousMap

namespace TauCeti

universe u

section Transport

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {R : Type u} [CommRing R]
  {p : C(E, B)}

/-- **Transport is a quasi-isomorphism of DG local systems**: for a transitive lifting function
`Φ`, the strict morphism `C_*(F') → C_*(F)_Φ` induced by transport is a quasi-isomorphism, since
transport is an equivariant homotopy equivalence. -/
theorem isQuasiIso_transportLocalSystemHom {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive)
    (b : B) : DGRightModuleCat.IsQuasiIso (transportLocalSystemHom (R := R) hΦ b) := by
  let := hΦ.mulAction b
  let := hΦ.continuousSMul b
  exact isQuasiIso_of_apply_eq (G' := MooreLoopSpace B b) R (transportLocalSystemHom hΦ b)
    (Φ.transportHomotopyEquiv b) fun x ↦ by
      rw [transportLocalSystemHom_apply]
      exact congrArg (fun k : C(_, _) ↦ cubicalChainModuleLinearMap R k x)
        (ContinuousMap.ext fun y ↦ congrFun (Φ.coe_transportHomotopyEquiv b) y).symm

/-- **The zigzag comparing two transitive lifting functions**: the roof
`C_*(F)_{Φ₀} ← C_*(F') → C_*(F)_{Φ₁}` of strict morphisms induced by transport, as a right fraction
for the quasi-isomorphisms, with no homotopy between `Φ₀` and `Φ₁`.  Its second leg is also a
quasi-isomorphism (`isQuasiIso_liftingLocalSystemRoof_f`). -/
def liftingLocalSystemRoof {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra B b R)).RightFraction
      (liftingLocalSystem (R := R) hΦ₀ b) (liftingLocalSystem hΦ₁ b) where
  X' := fibrationLocalSystem R p b
  s := transportLocalSystemHom hΦ₀ b
  hs := (DGRightModuleCat.quasiIsos_iff _).2 (isQuasiIso_transportLocalSystemHom hΦ₀ b)
  f := transportLocalSystemHom hΦ₁ b

/-- The apex of the zigzag is the DG local system `C_*(F')` of the Moore-path replacement. -/
@[simp]
theorem liftingLocalSystemRoof_X' {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).X' = fibrationLocalSystem R p b :=
  (rfl)

/-- The left leg of the zigzag is the strict morphism of transport along `Φ₀`, up to the identity
of the apex. -/
@[simp]
theorem liftingLocalSystemRoof_s {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).s =
      eqToHom (liftingLocalSystemRoof_X' hΦ₀ hΦ₁ b) ≫ transportLocalSystemHom hΦ₀ b := by
  unfold liftingLocalSystemRoof
  exact (Category.id_comp _).symm

/-- The right leg of the zigzag is the strict morphism of transport along `Φ₁`, up to the identity
of the apex. -/
@[simp]
theorem liftingLocalSystemRoof_f {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).f =
      eqToHom (liftingLocalSystemRoof_X' hΦ₀ hΦ₁ b) ≫ transportLocalSystemHom hΦ₁ b := by
  unfold liftingLocalSystemRoof
  exact (Category.id_comp _).symm

/-- The second leg of the zigzag is a quasi-isomorphism too. -/
theorem isQuasiIso_liftingLocalSystemRoof_f {Φ₀ Φ₁ : MooreLiftingFunction p}
    (hΦ₀ : Φ₀.IsTransitive) (hΦ₁ : Φ₁.IsTransitive) (b : B) :
    DGRightModuleCat.IsQuasiIso (liftingLocalSystemRoof (R := R) hΦ₀ hΦ₁ b).f := by
  exact isQuasiIso_transportLocalSystemHom hΦ₁ b

end Transport

section Derived

/-! ### The comparison in the derived category -/

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {R : Type u} [CommRing R]
  {p : C(E, B)} {b : B} {D : Type*} [Category* D] {L : DGLocalSystem B b R ⥤ D}
  (hL : (DGRightModuleCat.quasiIsos (loopChain_isDGAlgebra B b R)).IsInvertedBy L)

/-- **Transport as an isomorphism after inverting quasi-isomorphisms**: for a functor `L` out of
DG local systems that inverts quasi-isomorphisms, such as a localization functor to the derived
category or the cohomology functor, the image under `L` of transport `C_*(F') → C_*(F)_Φ` along a
transitive lifting function `Φ`. -/
def transportLocalSystemIso {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive) :
    L.obj (fibrationLocalSystem R p b) ≅ L.obj (liftingLocalSystem hΦ b) :=
  haveI := hL _ ((DGRightModuleCat.quasiIsos_iff _).2 (isQuasiIso_transportLocalSystemHom hΦ b))
  asIso (L.map (transportLocalSystemHom hΦ b))

@[simp]
theorem transportLocalSystemIso_hom {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive) :
    (transportLocalSystemIso hL hΦ).hom = L.map (transportLocalSystemHom hΦ b) :=
  (rfl)

/-- **The comparison of two transitive lifting functions** `Φ₀`, `Φ₁` in the derived category:
for a functor `L` out of DG local systems that inverts quasi-isomorphisms, the isomorphism
`L(C_*(F)_{Φ₀}) ≅ L(C_*(F)_{Φ₁})` given by the zigzag of transports
`C_*(F)_{Φ₀} ← C_*(F') → C_*(F)_{Φ₁}` (`TauCeti.liftingLocalSystemRoof`). For a localization
functor `L` at the quasi-isomorphisms, `Localization.inverts L _` supplies `hL`. -/
def liftingLocalSystemIso {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) :
    L.obj (liftingLocalSystem hΦ₀ b) ≅ L.obj (liftingLocalSystem hΦ₁ b) :=
  (transportLocalSystemIso hL hΦ₀).symm ≪≫ transportLocalSystemIso hL hΦ₁

/-- The comparison commutes with the transports: transport along `Φ₀` followed by the comparison is
transport along `Φ₁`. -/
@[reassoc (attr := simp)]
theorem map_transportLocalSystemHom_comp_liftingLocalSystemIso_hom
    {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive) (hΦ₁ : Φ₁.IsTransitive) :
    L.map (transportLocalSystemHom hΦ₀ b) ≫ (liftingLocalSystemIso hL hΦ₀ hΦ₁).hom =
      L.map (transportLocalSystemHom hΦ₁ b) := by
  simp [liftingLocalSystemIso, transportLocalSystemIso]

/-- The comparison is the image under `L` of the zigzag of transports, read as a right fraction. -/
theorem liftingLocalSystemIso_hom {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) :
    (liftingLocalSystemIso hL hΦ₀ hΦ₁).hom = (liftingLocalSystemRoof hΦ₀ hΦ₁ b).map L hL := by
  rw [← cancel_epi (transportLocalSystemIso hL hΦ₀).hom, transportLocalSystemIso_hom,
    map_transportLocalSystemHom_comp_liftingLocalSystemIso_hom]
  exact ((liftingLocalSystemRoof hΦ₀ hΦ₁ b).map_s_comp_map L hL).symm

/-- **Uniqueness of the comparison**: an isomorphism `L(C_*(F)_{Φ₀}) ≅ L(C_*(F)_{Φ₁})` that
commutes with the transports along `Φ₀` and `Φ₁` is the comparison. -/
theorem eq_liftingLocalSystemIso {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive)
    (e : L.obj (liftingLocalSystem hΦ₀ b) ≅ L.obj (liftingLocalSystem hΦ₁ b))
    (he : L.map (transportLocalSystemHom hΦ₀ b) ≫ e.hom = L.map (transportLocalSystemHom hΦ₁ b)) :
    e = liftingLocalSystemIso hL hΦ₀ hΦ₁ := by
  ext
  rw [← cancel_epi (transportLocalSystemIso hL hΦ₀).hom, transportLocalSystemIso_hom, he,
    map_transportLocalSystemHom_comp_liftingLocalSystemIso_hom]

/-- The comparison of a transitive lifting function with itself is the identity. -/
@[simp]
theorem liftingLocalSystemIso_self {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive) :
    liftingLocalSystemIso hL hΦ hΦ = Iso.refl _ :=
  Iso.symm_self_id _

/-- Reversing the comparison of `Φ₀` with `Φ₁` gives the comparison of `Φ₁` with `Φ₀`. -/
@[simp]
theorem liftingLocalSystemIso_symm {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) :
    (liftingLocalSystemIso hL hΦ₀ hΦ₁).symm = liftingLocalSystemIso hL hΦ₁ hΦ₀ := by
  ext
  simp [liftingLocalSystemIso]

/-- **The comparisons compose**: comparing `Φ₀` with `Φ₁` and then `Φ₁` with `Φ₂` is comparing
`Φ₀` with `Φ₂`. -/
@[simp]
theorem liftingLocalSystemIso_trans_liftingLocalSystemIso {Φ₀ Φ₁ Φ₂ : MooreLiftingFunction p}
    (hΦ₀ : Φ₀.IsTransitive) (hΦ₁ : Φ₁.IsTransitive) (hΦ₂ : Φ₂.IsTransitive) :
    liftingLocalSystemIso hL hΦ₀ hΦ₁ ≪≫ liftingLocalSystemIso hL hΦ₁ hΦ₂ =
      liftingLocalSystemIso hL hΦ₀ hΦ₂ := by
  ext
  simp [liftingLocalSystemIso]

/-- The inverse of the comparison of `Φ₀` with `Φ₁` is the comparison of `Φ₁` with `Φ₀`. -/
@[simp]
theorem liftingLocalSystemIso_inv {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive)
    (hΦ₁ : Φ₁.IsTransitive) :
    (liftingLocalSystemIso hL hΦ₀ hΦ₁).inv = (liftingLocalSystemIso hL hΦ₁ hΦ₀).hom :=
  congrArg Iso.hom (liftingLocalSystemIso_symm hL hΦ₀ hΦ₁)

/-- The comparison morphisms compose: comparing `Φ₀` with `Φ₁` and then `Φ₁` with `Φ₂` is
comparing `Φ₀` with `Φ₂`. -/
@[reassoc (attr := simp)]
theorem liftingLocalSystemIso_hom_comp_liftingLocalSystemIso_hom
    {Φ₀ Φ₁ Φ₂ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive) (hΦ₁ : Φ₁.IsTransitive)
    (hΦ₂ : Φ₂.IsTransitive) :
    (liftingLocalSystemIso hL hΦ₀ hΦ₁).hom ≫ (liftingLocalSystemIso hL hΦ₁ hΦ₂).hom =
      (liftingLocalSystemIso hL hΦ₀ hΦ₂).hom :=
  congrArg Iso.hom (liftingLocalSystemIso_trans_liftingLocalSystemIso hL hΦ₀ hΦ₁ hΦ₂)

/-- The comparison is natural in the functor `L`: its image under a functor `G` is the comparison
for `L ⋙ G`. -/
theorem mapIso_liftingLocalSystemIso {D' : Type*} [Category* D'] (G : D ⥤ D')
    {Φ₀ Φ₁ : MooreLiftingFunction p} (hΦ₀ : Φ₀.IsTransitive) (hΦ₁ : Φ₁.IsTransitive) :
    G.mapIso (liftingLocalSystemIso hL hΦ₀ hΦ₁) =
      liftingLocalSystemIso (MorphismProperty.IsInvertedBy.of_comp _ L hL G) hΦ₀ hΦ₁ := by
  refine eq_liftingLocalSystemIso (L := L ⋙ G) _ hΦ₀ hΦ₁ _ ?_
  simp [← G.map_comp]

end Derived

end TauCeti

end
