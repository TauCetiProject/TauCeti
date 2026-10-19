/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.DrinfeldBasis.Naive
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Naive
public import TauCeti.AlgebraicGeometry.ModularCurve.Gamma.Full
public import TauCeti.AlgebraicGeometry.ModularCurve.Gamma.One
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Comparison of Drinfeld and naive `[Γ₁(N)]`- and `[Γ(N)]`-structures

This file compares the integral Drinfeld moduli problems `[Γ₁(N)]` (`ModuliProblem.gammaOne`) and
`[Γ(N)]` (`ModuliProblem.gamma`) over `Ell/B` with their naive counterparts
(`ModuliProblem.gammaOneNaive`, `ModuliProblem.gammaNaive`), following Katz–Mazur §3.7:

1. **For `[Γ₁(N)]`**: over a base scheme `B` on which `N` is invertible, a point `P` of exact
   order `N` on an elliptic curve `E/S` over `B` gives the naive `[Γ₁(N)]`-structure `a ↦ aP`,
   injective on every fibre (`EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective`). This
   defines a monomorphism `[Γ₁(N)] ⟶ [Γ₁(N)]_naive` (`ModuliProblem.gammaOneToGammaOneNaive`),
   from which `[Γ₁(N)]` inherits the rigidity of `[Γ₁(N)]_naive` for `N ≥ 4`
   (`ModuliProblem.isRigid_gammaOne`).
2. **For `[Γ(N)]`**: over an arbitrary base `B`, every naive `[Γ(N)]`-structure is a Drinfeld
   basis (`EllipticCurveGeom.IsFiberwiseInjective.isDrinfeldBasis`), giving a
   `GL₂(ℤ/Nℤ)`-equivariant monomorphism `[Γ(N)]_naive ⟶ [Γ(N)]`
   (`ModuliProblem.gammaNaiveToGamma`). Over a base `B` on which `N` is invertible, every Drinfeld
   basis is conversely a naive `[Γ(N)]`-structure
   (`EllipticCurveGeom.IsDrinfeldBasis.isFiberwiseInjective`), giving the inverse morphism
   `[Γ(N)] ⟶ [Γ(N)]_naive` (`ModuliProblem.gammaToGammaNaive`) and the isomorphism
   `[Γ(N)] ≅ [Γ(N)]_naive` (`ModuliProblem.gammaIsoGammaNaive`). Over such a base, `[Γ(N)]`
   therefore inherits from `[Γ(N)]_naive` freeness of the `GL₂(ℤ/Nℤ)`-action over nonempty bases
   (`ModuliProblem.eq_one_of_gammaAction_hom_app_eq_self`), rigidity for `N ≥ 3`
   (`ModuliProblem.isRigid_gamma`), and étaleness over `Ell/B`
   (`ModuliProblem.hasProperty_etale_gammaRelRepData`), making `[Γ(N)]` finite étale over
   `Ell/B` together with `ModuliProblem.hasProperty_isFinite_gammaRelRepData`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneToGammaOneNaive B N hN`: the morphism from
  Drinfeld to naive `[Γ₁(N)]`-structures over a base `B` on which `N` is invertible.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveToGamma B N`: the morphism from naive to
  Drinfeld `[Γ(N)]`-structures over an arbitrary base `B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaToGammaNaive B N hN` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaIsoGammaNaive B N hN`: the inverse morphism and
  isomorphism `[Γ(N)] ≅ [Γ(N)]_naive` over a base `B` on which `N` is invertible.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.mono_gammaOneToGammaOneNaive` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_gammaOne`: where `N` is invertible on `B`,
  Drinfeld `[Γ₁(N)]`-structures form a subproblem of the naive ones, hence are rigid for `N ≥ 4`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaNaiveAction_hom_comp_gammaNaiveToGamma` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.gammaAction_hom_comp_gammaToGammaNaive`: the comparison
  morphisms between `[Γ(N)]` and `[Γ(N)]_naive` are `GL₂(ℤ/Nℤ)`-equivariant.
* `TauCeti.AlgebraicGeometry.ModuliProblem.eq_one_of_gammaAction_hom_app_eq_self`: where `N` is
  invertible on `B`, `GL₂(ℤ/Nℤ)` acts freely on `[Γ(N)]` over a nonempty base.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_gamma`: where `N` is invertible on `B`,
  `[Γ(N)]` is rigid for `N ≥ 3` (Katz–Mazur 2.7.2).
* `TauCeti.AlgebraicGeometry.ModuliProblem.hasProperty_etale_gammaRelRepData`: where `N` is
  invertible on `B`, `[Γ(N)]` is étale over `Ell/B` (Katz–Mazur 3.7.1).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.7.2 (rigidity for `N ≥ 3`),
  §3.1 (`[Γ(N)]`-structures), §3.2 (`[Γ₁(N)]`-structures), and §3.7 / 3.7.1 (comparison with
  naive level structures where `N` is invertible).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

namespace ModuliProblem

variable {B : Scheme.{u}} {N : ℕ} [NeZero N]

/-! ### `[Γ₁(N)]` where `N` is invertible -/

variable (B N) in
/-- **Drinfeld `[Γ₁(N)]`-structures are naive where `N` is invertible.** Over a base `B` on which
`N` is invertible, the point `P` of exact order `N` of a `[Γ₁(N)]`-structure gives the naive
`[Γ₁(N)]`-structure `a ↦ aP`, injective on every fibre by
`EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective`. This is natural in the object of
`Ell/B`. -/
noncomputable def gammaOneToGammaOneNaive (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    gammaOne B N ⟶ gammaOneNaive B N where
  app X := TypeCat.ofHom fun α ↦ (naiveLevelEquiv X.unop).symm
    ⟨(zmodMonoidHomEquiv N _).symm
        ⟨(gammaOneEquiv X.unop α).1, (gammaOneEquiv X.unop α).2.pow_eq_one⟩,
      EllipticCurveGeom.IsOfExactOrder.isFiberwiseInjective
        (by rw [← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]
            exact (gammaOneEquiv X.unop α).2)
        fun s ↦ X.unop.structureMap.natCast_residueField_ne_zero (hN _)⟩
  naturality X Y φ := by
    ext α
    apply (naiveLevelEquiv _).injective
    apply Subtype.ext
    apply (zmodMonoidHomEquiv N _).injective
    apply Subtype.ext
    simp only [op_unop, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, Equiv.apply_symm_apply, coe_zmodMonoidHomEquiv_apply]
    rw [← Quiver.Hom.op_unop φ, gammaOneEquiv_map, naiveLevelEquiv_map, Equiv.apply_symm_apply,
      MonoidHom.comp_apply, ← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]

variable {hN : ∀ b : B, (N : B.residueField b) ≠ 0}

/-- The naive `[Γ₁(N)]`-structure of a point `P` of exact order `N` sends `a` to `aP`. -/
@[simp]
theorem naiveLevelEquiv_gammaOneToGammaOneNaive_app_apply (X : EllObj B)
    (α : (gammaOne B N).obj (op X)) (a : ZMod N) :
    (naiveLevelEquiv X ((gammaOneToGammaOneNaive B N hN).app (op X) α)).1 (.ofAdd a) =
      (gammaOneEquiv X α).1 ^ a.val := by
  simp [gammaOneToGammaOneNaive]

/-- **Drinfeld `[Γ₁(N)]`-structures form a subproblem of the naive ones** where `N` is
invertible: a `[Γ₁(N)]`-structure is determined by its naive `[Γ₁(N)]`-structure. -/
instance mono_gammaOneToGammaOneNaive : Mono (gammaOneToGammaOneNaive B N hN) := by
  have (X : (EllObj B)ᵒᵖ) : Mono ((gammaOneToGammaOneNaive B N hN).app X) := by
    refine (mono_iff_injective _).mpr fun α β hαβ ↦ ?_
    apply (gammaOneEquiv X.unop).injective
    apply Subtype.ext
    have := congrArg (fun γ ↦ (naiveLevelEquiv X.unop γ).1 (.ofAdd 1)) hαβ
    simpa [gammaOneToGammaOneNaive, ← coe_zmodMonoidHomEquiv_apply] using this
  exact NatTrans.mono_of_mono_app _

variable (B N) in
/-- **`[Γ₁(N)]` is rigid for `N ≥ 4` where `N` is invertible.** Over a base `B` on which `N` is
invertible, `[Γ₁(N)]` maps to the rigid naive problem `[Γ₁(N)]_naive`
(`ModuliProblem.isRigid_gammaOneNaive`). -/
theorem isRigid_gammaOne (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (hN4 : 4 ≤ N) :
    (gammaOne B N).IsRigid :=
  (isRigid_gammaOneNaive B N hN4).of_hom (gammaOneToGammaOneNaive B N hN)

/-! ### `[Γ(N)]` and `[Γ(N)]_naive` -/

variable (B N) in
/-- **Naive `[Γ(N)]`-structures are Drinfeld bases over every base.** The morphism of moduli
problems `[Γ(N)]_naive ⟶ [Γ(N)]` over `Ell/B` sending a homomorphism `(ℤ/Nℤ)² →* E(S)` injective on
every fibre to the Drinfeld basis it defines
(`EllipticCurveGeom.IsFiberwiseInjective.isDrinfeldBasis`). No invertibility hypothesis on `N` is
needed. -/
noncomputable def gammaNaiveToGamma : gammaNaive B N ⟶ gamma B N where
  app X := TypeCat.ofHom fun α ↦ (gammaEquiv X.unop).symm
    ⟨(naiveLevelEquiv X.unop α).1, (naiveLevelEquiv X.unop α).2.isDrinfeldBasis⟩
  naturality X Y φ := by
    ext α
    apply (gammaEquiv _).injective
    apply Subtype.ext
    simp only [op_unop, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, Equiv.apply_symm_apply]
    rw [← Quiver.Hom.op_unop φ, gammaEquiv_map, naiveLevelEquiv_map, Equiv.apply_symm_apply]

/-- `gammaNaiveToGamma` preserves the underlying homomorphism `(ℤ/Nℤ)² →* E(S)`. -/
@[simp]
theorem gammaEquiv_gammaNaiveToGamma_app (X : EllObj B) (α : (gammaNaive B N).obj (op X)) :
    (gammaEquiv X ((gammaNaiveToGamma B N).app (op X) α)).1 = (naiveLevelEquiv X α).1 := by
  simp [gammaNaiveToGamma]

/-- **Naive `[Γ(N)]`-structures form a subproblem of Drinfeld `[Γ(N)]`-structures** over every
base. -/
instance mono_gammaNaiveToGamma : Mono (gammaNaiveToGamma B N) := by
  have (X : (EllObj B)ᵒᵖ) : Mono ((gammaNaiveToGamma B N).app X) := by
    refine (mono_iff_injective _).mpr fun α β hαβ ↦ ?_
    apply (naiveLevelEquiv X.unop).injective
    apply Subtype.ext
    simpa [gammaNaiveToGamma] using congrArg (fun γ ↦ (gammaEquiv X.unop γ).1) hαβ
  exact NatTrans.mono_of_mono_app _

variable (B N) in
/-- **The comparison `[Γ(N)]_naive ⟶ [Γ(N)]` is `GL₂(ℤ/Nℤ)`-equivariant.** -/
@[reassoc (attr := simp)]
theorem gammaNaiveAction_hom_comp_gammaNaiveToGamma (g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ) :
    (gammaNaiveAction B N g).asIso.hom ≫ gammaNaiveToGamma B N =
      gammaNaiveToGamma B N ≫ (gammaAction B N g).asIso.hom := by
  ext X α a
  simp

variable (B N) in
/-- **Drinfeld `[Γ(N)]`-structures are naive where `N` is invertible** (Katz–Mazur, §3.7). Over a
base `B` on which `N` is invertible, every Drinfeld basis `(ℤ/Nℤ)² →* E(S)` is injective on every
fibre (`EllipticCurveGeom.IsDrinfeldBasis.isFiberwiseInjective`), defining a morphism of moduli
problems `[Γ(N)] ⟶ [Γ(N)]_naive` inverse to `gammaNaiveToGamma`. -/
noncomputable def gammaToGammaNaive (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    gamma B N ⟶ gammaNaive B N where
  app X := TypeCat.ofHom fun α ↦ (naiveLevelEquiv X.unop).symm
    ⟨(gammaEquiv X.unop α).1, (gammaEquiv X.unop α).2.isFiberwiseInjective fun _ ↦
      X.unop.structureMap.natCast_residueField_ne_zero (hN _)⟩
  naturality X Y φ := by
    ext α
    apply (naiveLevelEquiv _).injective
    apply Subtype.ext
    simp only [op_unop, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, Equiv.apply_symm_apply]
    rw [← Quiver.Hom.op_unop φ, naiveLevelEquiv_map, gammaEquiv_map, Equiv.apply_symm_apply]

/-- `gammaToGammaNaive` preserves the underlying homomorphism `(ℤ/Nℤ)² →* E(S)`. -/
@[simp]
theorem naiveLevelEquiv_gammaToGammaNaive_app (X : EllObj B) (α : (gamma B N).obj (op X)) :
    (naiveLevelEquiv X ((gammaToGammaNaive B N hN).app (op X) α)).1 = (gammaEquiv X α).1 := by
  simp [gammaToGammaNaive]

/-- `gammaToGammaNaive` and `gammaNaiveToGamma` compose to the identity on `[Γ(N)]`. -/
@[reassoc (attr := simp)]
theorem gammaToGammaNaive_comp_gammaNaiveToGamma :
    gammaToGammaNaive B N hN ≫ gammaNaiveToGamma B N = 𝟙 (gamma B N) := by
  ext X α a
  simp

/-- `gammaNaiveToGamma` and `gammaToGammaNaive` compose to the identity on `[Γ(N)]_naive`. -/
@[reassoc (attr := simp)]
theorem gammaNaiveToGamma_comp_gammaToGammaNaive :
    gammaNaiveToGamma B N ≫ gammaToGammaNaive B N hN = 𝟙 (gammaNaive B N) := by
  ext X α a
  simp

variable (B N) in
/-- **Drinfeld and naive `[Γ(N)]`-structures coincide where `N` is invertible** (Katz–Mazur, §3.7):
over a base `B` on which `N` is invertible, `gammaToGammaNaive` and `gammaNaiveToGamma` are
mutually inverse isomorphisms between `[Γ(N)]` and `[Γ(N)]_naive`. -/
noncomputable def gammaIsoGammaNaive (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    gamma B N ≅ gammaNaive B N where
  hom := gammaToGammaNaive B N hN
  inv := gammaNaiveToGamma B N
  hom_inv_id := gammaToGammaNaive_comp_gammaNaiveToGamma
  inv_hom_id := gammaNaiveToGamma_comp_gammaToGammaNaive

@[simp]
theorem gammaIsoGammaNaive_hom :
    (gammaIsoGammaNaive B N hN).hom = gammaToGammaNaive B N hN :=
  (rfl)

@[simp]
theorem gammaIsoGammaNaive_inv :
    (gammaIsoGammaNaive B N hN).inv = gammaNaiveToGamma B N :=
  (rfl)

/-- Where `N` is invertible on `B`, `gammaToGammaNaive` is an isomorphism. -/
instance isIso_gammaToGammaNaive : IsIso (gammaToGammaNaive B N hN) :=
  (gammaIsoGammaNaive B N hN).isIso_hom

/-- Where `N` is invertible on `B`, `gammaNaiveToGamma` is an isomorphism. -/
theorem isIso_gammaNaiveToGamma (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    IsIso (gammaNaiveToGamma B N) :=
  (gammaIsoGammaNaive B N hN).isIso_inv

/-- **The comparison `[Γ(N)] ⟶ [Γ(N)]_naive` is `GL₂(ℤ/Nℤ)`-equivariant.** -/
@[reassoc (attr := simp)]
theorem gammaAction_hom_comp_gammaToGammaNaive (g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ) :
    (gammaAction B N g).asIso.hom ≫ gammaToGammaNaive B N hN =
      gammaToGammaNaive B N hN ≫ (gammaNaiveAction B N g).asIso.hom := by
  ext X α a
  simp

/-- **Where `N` is invertible, `GL₂(ℤ/Nℤ)` acts freely on `[Γ(N)]` over a nonempty base.** -/
theorem eq_one_of_gammaAction_hom_app_eq_self {X : EllObj B} [Nonempty X.base]
    (hN : ∀ b : B, (N : B.residueField b) ≠ 0) {g : (GL (Fin 2) (ZMod N))ᵐᵒᵖ}
    {α : (gamma B N).obj (op X)} (h : (gammaAction B N g).asIso.hom.app (op X) α = α) :
    g = 1 := by
  apply eq_one_of_gammaNaiveAction_hom_app_eq_self (α := (gammaToGammaNaive B N hN).app (op X) α)
  have h' := congrArg ((gammaToGammaNaive B N hN).app (op X)) h
  have hcomp := congrArg (fun f : gamma B N ⟶ gammaNaive B N ↦ f.app (op X) α)
    (gammaAction_hom_comp_gammaToGammaNaive (hN := hN) g)
  exact hcomp.symm.trans h'

variable (B N) in
/-- **`[Γ(N)]` is rigid for `N ≥ 3` where `N` is invertible** (Katz–Mazur, 2.7.2). Over a base `B`
on which `N` is invertible, `[Γ(N)]` is isomorphic to the rigid naive problem `[Γ(N)]_naive`
(`ModuliProblem.isRigid_gammaNaive`). -/
theorem isRigid_gamma (hN : ∀ b : B, (N : B.residueField b) ≠ 0) (hN3 : 3 ≤ N) :
    (gamma B N).IsRigid :=
  (isRigid_gammaNaive B N hN3).of_hom (gammaToGammaNaive B N hN)

variable (B N) in
/-- **The moduli problem `[Γ(N)]` is étale over `Ell/B` when `N` is invertible on `B`**
(Katz–Mazur, 3.7.1): where `N` is invertible on `B`, `[Γ(N)]` is isomorphic to `[Γ(N)]_naive`,
whose representing schemes are étale over their bases. Together with
`ModuliProblem.hasProperty_isFinite_gammaRelRepData`, this makes `[Γ(N)]` finite étale over
`Ell/B`. -/
theorem hasProperty_etale_gammaRelRepData (hN : ∀ b : B, (N : B.residueField b) ≠ 0) :
    (gammaRelRepData B N).HasProperty @Etale := by
  exact ((gammaRelRepData B N).hasProperty_iff_of_iso gammaNaiveRelRepData
    (gammaIsoGammaNaive B N hN) @Etale).mpr (hasProperty_etale_gammaNaiveRelRepData hN)

end ModuliProblem

end TauCeti.AlgebraicGeometry
