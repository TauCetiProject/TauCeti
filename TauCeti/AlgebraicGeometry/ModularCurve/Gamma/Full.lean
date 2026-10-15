/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Locus
public import TauCeti.AlgebraicGeometry.ModularCurve.FullLevel
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.MulBy.Rank

/-!
# Relative representability of `[Γ(N)]`

Let `E/S` be an elliptic curve and `N` a positive integer. The product
`E[N] ×_S E[N]` carries the universal homomorphism `(ℤ/Nℤ)² →* E`. After base changing `E` to
this product, being a Drinfeld basis is a closed condition. Its closed locus is the scheme
`EllObj.drinfeldBasisScheme X N`.

For every scheme `T` over `S`, morphisms from `T` to this closed locus are naturally equivalent to
Drinfeld bases of the base change `E_T` (`ModuliProblem.gammaBaseChangeEquiv`). Consequently the
integral moduli problem `[Γ(N)]` is relatively representable by a finite scheme over every object
of `Ell/B` (`ModuliProblem.gammaRelRepData` and
`ModuliProblem.hasProperty_isFinite_gammaRelRepData`). No invertibility hypothesis on `N` is used.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllObj.drinfeldBasisScheme`: the closed subscheme of
  `E[N] ×_S E[N]` parametrising Drinfeld bases.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaBaseChangeEquiv`: the natural equivalence between
  points of that scheme and `[Γ(N)]`-structures on a base change.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaRelRepData`: relative-representability data for
  `[Γ(N)]`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §3.1 and Theorem 3.6.0.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllObj

variable {B : Scheme.{u}} (X : EllObj B) (N : ℕ) [NeZero N]

/-- The ambient scheme `E[N] ×_S E[N]` carrying the universal pair of `N`-torsion points. -/
noncomputable abbrev drinfeldBasisAmbient : Over X.base :=
  (X.curve.torsion N).X ⊗ (X.curve.torsion N).X

/-- The universal homomorphism `(ℤ/Nℤ)² →* E_H(H)`, where
`H = E[N] ×_S E[N]`, obtained from the universal pair of points after base changing `E` to `H`. -/
noncomputable def universalDrinfeldBasisHom : Multiplicative (ZMod N × ZMod N) →*
    (𝟙_ (Over (X.baseChangeFunctor.obj (X.drinfeldBasisAmbient N)).base) ⟶
      Over.mk (X.baseChangeFunctor.obj (X.drinfeldBasisAmbient N)).curve.structureMap) :=
  (X.baseChangePointsEquiv (X.drinfeldBasisAmbient N)).symm.toMonoidHom.comp
    (X.curve.torsionPairHom N)

/-- The universal Drinfeld-basis homomorphism corresponds to the universal pair of torsion points
under the equivalence between points of a base change and points with values in its base. -/
@[simp]
theorem baseChangePointsEquiv_universalDrinfeldBasisHom
    (a : Multiplicative (ZMod N × ZMod N)) :
    X.baseChangePointsEquiv (X.drinfeldBasisAmbient N) (X.universalDrinfeldBasisHom N a) =
      X.curve.torsionPairHom N a :=
  MulEquiv.apply_symm_apply _ _

/-- Pulling the universal Drinfeld-basis homomorphism back along a point `x` of
`E[N] ×_S E[N]` gives the pair of torsion points classified by `x`. -/
theorem baseChangePointsEquiv_pointsPullback_universalDrinfeldBasisHom {T : Over X.base}
    (x : T ⟶ X.drinfeldBasisAmbient N) (a : Multiplicative (ZMod N × ZMod N)) :
    X.baseChangePointsEquiv T (EllipticCurveGeom.pointsPullback
        (X.baseChangeFunctor.map x).isPullback (X.baseChangeFunctor.map x).zero_total
        (X.universalDrinfeldBasisHom N a)) =
      x ≫ X.curve.torsionPairHom N a := by
  rw [baseChangePointsEquiv_pointsPullback, baseChangePointsEquiv_universalDrinfeldBasisHom]

/-- Pulling the universal Drinfeld-basis homomorphism back along a point `x` of
`E[N] ×_S E[N]` gives `ψ` exactly when `x` classifies the pair of torsion points underlying
`ψ`. -/
theorem pointsPullback_comp_universalDrinfeldBasisHom_eq_iff {T : Over X.base}
    (x : T ⟶ X.drinfeldBasisAmbient N)
    (ψ : Multiplicative (ZMod N × ZMod N) →*
      (𝟙_ (Over (X.baseChangeFunctor.obj T).base) ⟶
        Over.mk (X.baseChangeFunctor.obj T).curve.structureMap)) :
    (EllipticCurveGeom.pointsPullback (X.baseChangeFunctor.map x).isPullback
        (X.baseChangeFunctor.map x).zero_total).comp (X.universalDrinfeldBasisHom N) = ψ ↔
      ∀ a, x ≫ X.curve.torsionPairHom N a = X.baseChangePointsEquiv T (ψ a) := by
  simp only [MonoidHom.ext_iff, MonoidHom.comp_apply,
    ← (X.baseChangePointsEquiv T).injective.eq_iff,
    baseChangePointsEquiv_pointsPullback_universalDrinfeldBasisHom]

/-- The ideal sheaf on `E[N] ×_S E[N]` cutting out the locus where its universal pair is a
Drinfeld basis. -/
noncomputable def universalDrinfeldBasisLocus :
    (X.drinfeldBasisAmbient N).left.IdealSheafData :=
  (X.baseChangeFunctor.obj (X.drinfeldBasisAmbient N)).curve.drinfeldBasisLocus N
    (X.universalDrinfeldBasisHom N)

/-- The finite `S`-scheme parametrising Drinfeld bases of `E[N]`: the closed subscheme of
`E[N] ×_S E[N]` on which the universal pair is a Drinfeld basis. -/
noncomputable abbrev drinfeldBasisScheme : Over X.base :=
  Over.mk ((X.universalDrinfeldBasisLocus N).subschemeι ≫ (X.drinfeldBasisAmbient N).hom)

/-- The closed immersion from the Drinfeld-basis scheme to `E[N] ×_S E[N]`. -/
noncomputable abbrev drinfeldBasisSchemeι : X.drinfeldBasisScheme N ⟶
    X.drinfeldBasisAmbient N :=
  Over.homMk (X.universalDrinfeldBasisLocus N).subschemeι

/-- A point `x` of `E[N] ×_S E[N]` along which the universal pair pulls back to a Drinfeld basis
lifts to the Drinfeld-basis scheme. -/
noncomputable def liftDrinfeldBasisScheme {T : Over X.base} (x : T ⟶ X.drinfeldBasisAmbient N)
    (hx : (X.baseChangeFunctor.obj T).curve.IsDrinfeldBasis N
      ((EllipticCurveGeom.pointsPullback (X.baseChangeFunctor.map x).isPullback
        (X.baseChangeFunctor.map x).zero_total).comp (X.universalDrinfeldBasisHom N))) :
    T ⟶ X.drinfeldBasisScheme N :=
  Over.homMk
    (IsClosedImmersion.lift (X.universalDrinfeldBasisLocus N).subschemeι x.left (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff _ _ _).mp hx))
    (by
      dsimp only [drinfeldBasisScheme, Over.mk_hom]
      rw [← Category.assoc, IsClosedImmersion.lift_fac]
      exact x.w)

/-- The lift of `x` to the Drinfeld-basis scheme factors `x` through the closed immersion. -/
@[reassoc (attr := simp)]
theorem liftDrinfeldBasisScheme_drinfeldBasisSchemeι {T : Over X.base}
    (x : T ⟶ X.drinfeldBasisAmbient N)
    (hx : (X.baseChangeFunctor.obj T).curve.IsDrinfeldBasis N
      ((EllipticCurveGeom.pointsPullback (X.baseChangeFunctor.map x).isPullback
        (X.baseChangeFunctor.map x).zero_total).comp (X.universalDrinfeldBasisHom N))) :
    X.liftDrinfeldBasisScheme N x hx ≫ X.drinfeldBasisSchemeι N = x :=
  Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)

/-- The Drinfeld-basis scheme is finite over the base. -/
instance isFinite_drinfeldBasisScheme_hom : IsFinite (X.drinfeldBasisScheme N).hom := by
  have := X.curve.isFinite_torsion_hom (n := (N : ℤ)) (by exact_mod_cast NeZero.ne N)
  have : IsFinite (X.drinfeldBasisAmbient N).hom := by
    dsimp only [drinfeldBasisAmbient]
    rw [Over.tensorObj_hom]
    infer_instance
  dsimp only [drinfeldBasisScheme, Over.mk_hom]
  infer_instance

end EllObj

namespace ModuliProblem

variable {B : Scheme.{u}} {N : ℕ} [NeZero N]

section RelRep

variable (X : EllObj B)

/-- The homomorphism defining the `[Γ(N)]`-structure associated to a point of the
Drinfeld-basis scheme. -/
noncomputable def gammaStructureOfSchemeHom {T : Over X.base}
    (y : T ⟶ X.drinfeldBasisScheme N) :
    Multiplicative (ZMod N × ZMod N) →*
      (𝟙_ (Over (X.baseChangeFunctor.obj T).base) ⟶
        Over.mk (X.baseChangeFunctor.obj T).curve.structureMap) :=
  { toFun a := (X.baseChangePointsEquiv T).symm
      (y ≫ X.drinfeldBasisSchemeι N ≫ X.curve.torsionPairHom N a)
    map_one' := by simp
    map_mul' a b := by simp [MonObj.comp_mul] }

@[simp]
theorem baseChangePointsEquiv_gammaStructureOfSchemeHom {T : Over X.base}
    (y : T ⟶ X.drinfeldBasisScheme N) (a : Multiplicative (ZMod N × ZMod N)) :
    X.baseChangePointsEquiv T (gammaStructureOfSchemeHom X y a) =
      y ≫ X.drinfeldBasisSchemeι N ≫ X.curve.torsionPairHom N a :=
  MulEquiv.apply_symm_apply _ _

theorem isDrinfeldBasis_gammaStructureOfSchemeHom {T : Over X.base}
    (y : T ⟶ X.drinfeldBasisScheme N) :
    (X.baseChangeFunctor.obj T).curve.IsDrinfeldBasis N
      (gammaStructureOfSchemeHom X y) := by
  let x : T ⟶ X.drinfeldBasisAmbient N := y ≫ X.drinfeldBasisSchemeι N
  let k := X.baseChangeFunctor.map x
  have heq := (EllObj.pointsPullback_comp_universalDrinfeldBasisHom_eq_iff X N x
    (gammaStructureOfSchemeHom X y)).2 fun a ↦ by simp [x]
  rw [← heq]
  apply (EllipticCurveGeom.isDrinfeldBasis_pointsPullback_iff k.isPullback k.zero_total _).2
  exact (Scheme.IdealSheafData.ker_subschemeι _).symm.le.trans (y.left.le_ker_comp _)

/-- **`[Γ(N)]`-structures on base changes are points of the Drinfeld-basis scheme.** For an object
`X = (E/S)` of `Ell/B` and a scheme `T` over `S`, Drinfeld bases of `E_T[N]` correspond naturally
to morphisms `T ⟶ X.drinfeldBasisScheme N` over `S`. -/
noncomputable def gammaBaseChangeEquiv (T : Over X.base) :
    (gamma B N).obj (op (X.baseChangeFunctor.obj T)) ≃
      (T ⟶ X.drinfeldBasisScheme N) := by
  let toStructure := fun y : T ⟶ X.drinfeldBasisScheme N ↦
    (gammaEquiv _).symm
      ⟨gammaStructureOfSchemeHom X y, isDrinfeldBasis_gammaStructureOfSchemeHom X y⟩
  refine (Equiv.ofBijective toStructure ?_).symm
  constructor
  · intro y y' h
    dsimp [toStructure] at h
    have h' := congrArg (fun α ↦ (gammaEquiv _ α).1) h
    simp only [Equiv.apply_symm_apply] at h'
    have hyy' : ∀ a,
        ((y' ≫ X.drinfeldBasisSchemeι N) ≫ X.curve.torsionPairHom N a) =
          (y ≫ X.drinfeldBasisSchemeι N) ≫ X.curve.torsionPairHom N a := fun a ↦ by
      simpa using
        (congrArg (X.baseChangePointsEquiv T) (DFunLike.congr_fun h' a)).symm
    rw [← cancel_mono (X.drinfeldBasisSchemeι N)]
    exact (X.curve.existsUnique_comp_torsionPairHom N
      ((X.baseChangePointsEquiv T).toMonoidHom.comp
        (gammaStructureOfSchemeHom X y))).unique
        (fun a ↦ by
          simp only [MonoidHom.coe_comp, Function.comp_apply]
          simp)
        (fun a ↦ by simpa using hyy' a)
  · intro α
    obtain ⟨⟨ψ, hψ⟩, rfl⟩ := (gammaEquiv _).symm.surjective α
    obtain ⟨x, hx, -⟩ := X.curve.existsUnique_comp_torsionPairHom N
      ((X.baseChangePointsEquiv T).toMonoidHom.comp ψ)
    have heq := (EllObj.pointsPullback_comp_universalDrinfeldBasisHom_eq_iff X N x ψ).2 hx
    refine ⟨X.liftDrinfeldBasisScheme N x (heq ▸ hψ), ?_⟩
    dsimp [toStructure]
    apply (gammaEquiv _).injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply MonoidHom.ext
    intro a
    apply (X.baseChangePointsEquiv T).injective
    simpa using hx a

/-- The point of the Drinfeld-basis scheme attached to the structure defined by a point `y` is
`y` itself. -/
@[simp]
theorem gammaBaseChangeEquiv_apply_symm_apply (T : Over X.base)
    (y : T ⟶ X.drinfeldBasisScheme N) :
    gammaBaseChangeEquiv X T ((gammaEquiv _).symm
      ⟨gammaStructureOfSchemeHom X y, isDrinfeldBasis_gammaStructureOfSchemeHom X y⟩) = y :=
  Equiv.apply_symm_apply _ _

/-- The inverse of `gammaBaseChangeEquiv` sends a point to its associated universal
`[Γ(N)]`-structure. -/
theorem gammaBaseChangeEquiv_symm_apply (T : Over X.base)
    (y : T ⟶ X.drinfeldBasisScheme N) :
    (gammaBaseChangeEquiv X T).symm y = (gammaEquiv _).symm
      ⟨gammaStructureOfSchemeHom X y, isDrinfeldBasis_gammaStructureOfSchemeHom X y⟩ := by
  apply (gammaBaseChangeEquiv X T).injective
  rw [Equiv.apply_symm_apply, gammaBaseChangeEquiv_apply_symm_apply]

/-- The `[Γ(N)]`-structure associated to a point commutes with base change. -/
theorem pointsPullback_gammaStructureOfSchemeHom {T' T : Over X.base} (k : T' ⟶ T)
    (y : T ⟶ X.drinfeldBasisScheme N) :
    (EllipticCurveGeom.pointsPullback (X.baseChangeFunctor.map k).isPullback
      (X.baseChangeFunctor.map k).zero_total).comp (gammaStructureOfSchemeHom X y) =
        gammaStructureOfSchemeHom X (k ≫ y) := by
  apply MonoidHom.ext
  intro a
  apply (X.baseChangePointsEquiv T').injective
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  rw [EllObj.baseChangePointsEquiv_pointsPullback]
  simp [gammaStructureOfSchemeHom]

/-- Naturality of `gammaBaseChangeEquiv`: pulling a `[Γ(N)]`-structure back along
`k : T' ⟶ T` precomposes its point of the Drinfeld-basis scheme with `k`. -/
theorem gammaBaseChangeEquiv_map {T' T : Over X.base} (k : T' ⟶ T)
    (α : (gamma B N).obj (op (X.baseChangeFunctor.obj T))) :
    gammaBaseChangeEquiv X T'
        ((gamma B N).map (X.baseChangeFunctor.map k).op α) =
      k ≫ gammaBaseChangeEquiv X T α := by
  obtain ⟨y, rfl⟩ := (gammaBaseChangeEquiv X T).symm.surjective α
  rw [gammaBaseChangeEquiv_symm_apply]
  have hmap : (gamma B N).map (X.baseChangeFunctor.map k).op
        ((gammaEquiv _).symm ⟨gammaStructureOfSchemeHom X y,
          isDrinfeldBasis_gammaStructureOfSchemeHom X y⟩) =
      (gammaEquiv _).symm ⟨gammaStructureOfSchemeHom X (k ≫ y),
        isDrinfeldBasis_gammaStructureOfSchemeHom X (k ≫ y)⟩ := by
    apply (gammaEquiv _).injective
    apply Subtype.ext
    rw [gammaEquiv_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact pointsPullback_gammaStructureOfSchemeHom X k y
  rw [hmap]
  simp only [gammaBaseChangeEquiv_apply_symm_apply]

/-- Naturality of `gammaBaseChangeEquiv`, read backwards. -/
theorem gammaBaseChangeEquiv_symm_comp {T' T : Over X.base} (k : T' ⟶ T)
    (y : T ⟶ X.drinfeldBasisScheme N) :
    (gammaBaseChangeEquiv X T').symm (k ≫ y) =
      (gamma B N).map (X.baseChangeFunctor.map k).op ((gammaBaseChangeEquiv X T).symm y) := by
  rw [Equiv.symm_apply_eq, gammaBaseChangeEquiv_map, Equiv.apply_symm_apply]

end RelRep

variable (B N) in
/-- **The integral moduli problem `[Γ(N)]` is relatively representable** (Katz–Mazur, 3.6.0).
For an elliptic curve `E/S`, it is represented by the closed Drinfeld-basis locus in
`E[N] ×_S E[N]`. -/
noncomputable def gammaRelRepData : (gamma B N).RelRepData where
  rep X := X.drinfeldBasisScheme N
  representableBy X :=
    { homEquiv := (gammaBaseChangeEquiv X _).symm
      homEquiv_comp k y := (gammaBaseChangeEquiv_symm_comp X k y).trans rfl }

/-- The scheme representing `[Γ(N)]`-structures on base changes of `X = (E/S)` is the closed
Drinfeld-basis locus in `E[N] ×_S E[N]`. -/
@[simp]
theorem gammaRelRepData_rep (X : EllObj B) :
    (gammaRelRepData B N).rep X = X.drinfeldBasisScheme N :=
  (rfl)

/-- The `[Γ(N)]`-structure on `E_T` of a morphism from `T` to the representing scheme is the one
given by `gammaBaseChangeEquiv`, after identifying the representing scheme with the
Drinfeld-basis scheme through `gammaRelRepData_rep`. -/
@[simp]
theorem gammaRelRepData_homEquiv (X : EllObj B) {T : Over X.base}
    (y : T ⟶ (gammaRelRepData B N).rep X) :
    ((gammaRelRepData B N).representableBy X).homEquiv y =
      (gammaBaseChangeEquiv X T).symm (y ≫ eqToHom (gammaRelRepData_rep X)) :=
  congrArg (gammaBaseChangeEquiv X T).symm (Category.comp_id y).symm

variable (B N) in
/-- **The integral moduli problem `[Γ(N)]` is finite over `Ell/B`** (Katz–Mazur, 3.6.0): its
representing scheme is a closed subscheme of `E[N] ×_S E[N]`. -/
theorem hasProperty_isFinite_gammaRelRepData :
    (gammaRelRepData B N).HasProperty @IsFinite :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦
    EllObj.isFinite_drinfeldBasisScheme_hom X N

end ModuliProblem

end TauCeti.AlgebraicGeometry
